/* =====================================================================
   Water Sort Solver
   100% offline. No network requests, no libraries, no AI: plain BFS.

   Sections
     1. Data       default palette + acceptance-test examples
     2. Solver     breadth-first search (runs inside a Web Worker)
     3. Verifier   independent strict replay of the found moves
     4. Runner     starts the worker (or a main-thread fallback)
     5. App / UI   setup, palette, board, validation, player
   ===================================================================== */
'use strict';

/* ---------------------------------------------------------------------
   1. DATA
   --------------------------------------------------------------------- */
var DEFAULT_PALETTE = [
  { id: 0, name: 'red',       hex: '#e0262f' },
  { id: 1, name: 'orange',    hex: '#ff8a00' },
  { id: 2, name: 'yellow',    hex: '#f7d92b' },
  { id: 3, name: 'green',     hex: '#2fa84f' },
  { id: 4, name: 'blue',      hex: '#1f4fe0' },
  { id: 5, name: 'lightblue', hex: '#59c8f5' },
  { id: 6, name: 'purple',    hex: '#7a35c4' },
  { id: 7, name: 'pink',      hex: '#ff7eb6' }
];

// Layers are listed TOP to BOTTOM (as the user reads them on screen).
var EXAMPLES = [
  { key: '27', name: 'Level 27', expected: 26, empties: 2, tubes: [
    ['green','blue','green','red'], ['blue','purple','purple','lightblue'],
    ['lightblue','orange','orange','lightblue'], ['yellow','orange','red','pink'],
    ['purple','yellow','green','pink'], ['red','purple','pink','lightblue'],
    ['pink','green','yellow','blue'], ['red','orange','yellow','blue'] ] },
  { key: '28', name: 'Level 28', expected: 22, empties: 2, tubes: [
    ['lightblue','red','lightblue','blue'], ['yellow','yellow','red','orange'],
    ['red','blue','blue','orange'], ['green','purple','green','blue'],
    ['lightblue','orange','purple','yellow'], ['yellow','orange','lightblue','purple'],
    ['purple','green','red','green'] ] },
  { key: '29', name: 'Level 29', expected: 24, empties: 2, tubes: [
    ['green','blue','yellow','orange'], ['yellow','red','yellow','pink'],
    ['orange','green','blue','purple'], ['lightblue','red','purple','purple'],
    ['orange','orange','pink','lightblue'], ['red','lightblue','blue','lightblue'],
    ['pink','green','red','yellow'], ['blue','pink','purple','green'] ] }
];

/* Convert an example into tubes of palette ids, each tube listed BOTTOM -> TOP
   (the internal order everywhere in this file). Empty tubes are appended. */
function exampleToTubes(ex) {
  var idByName = {};
  DEFAULT_PALETTE.forEach(function (c) { idByName[c.name] = c.id; });
  var tubes = ex.tubes.map(function (t) {
    return t.map(function (n) { return idByName[n]; }).reverse();
  });
  for (var i = 0; i < ex.empties; i++) tubes.push([]);
  return tubes;
}

/* ---------------------------------------------------------------------
   2. SOLVER  (breadth-first search)

   makeSolver is written as a self-contained function (no outside
   references) so that its source text can be handed to a Web Worker.

   Representation
     A tube is a string, one char per layer, BOTTOM first, TOP last.
     A state is an array of tube strings. In the BFS queue a state is
     stored as its tubes joined with "|" in the ORIGINAL tube order,
     so every recorded move already uses the user's tube numbers.

   Why BFS?  Every move costs 1, so the first time BFS reaches a solved
   state it has found a shortest solution. It also finds one whenever
   one exists (the search space is finite).

   Deduplication key (canonKey)
     Two states are "the same puzzle" if one can be turned into the other
     by (a) reordering tubes or (b) renaming colors. The key sorts the
     tubes, renames colors by first appearance, and sorts again. Equal
     keys always mean equivalent states, so skipping them keeps BFS exact
     (it may miss a few equivalences, which only costs speed, never
     correctness).

   Move rules (see genMoves)
     - pour the WHOLE top block of one color; if the target has room for
       only part of it, only that part moves
     - target needs free space AND (is empty OR same color on top)
     - never pour out of an already complete tube (full, one color)
     - never pour a uniform tube into an empty tube (no progress)
   --------------------------------------------------------------------- */
function makeSolver(startTubes, cap, limit) {
  var map = new Uint8Array(128);

  function isGoal(tubes) {
    for (var i = 0; i < tubes.length; i++) {
      var t = tubes[i];
      if (t.length === 0) continue;
      if (t.length !== cap) return false;
      for (var j = 1; j < t.length; j++) if (t[j] !== t[0]) return false;
    }
    return true;
  }

  function canonKey(tubes) {
    var s = tubes.slice().sort();
    map.fill(0);
    var next = 0, out = new Array(s.length);
    for (var i = 0; i < s.length; i++) {
      var t = s[i], r = '';
      for (var j = 0; j < t.length; j++) {
        var c = t.charCodeAt(j);
        if (!map[c]) map[c] = ++next;
        r += String.fromCharCode(47 + map[c]);
      }
      out[i] = r;
    }
    out.sort();
    return out.join('|');
  }

  /* All legal moves from a state as [from, to, count]. */
  function genMoves(tubes) {
    var moves = [];
    for (var i = 0; i < tubes.length; i++) {
      var s = tubes[i], L = s.length;
      if (L === 0) continue;
      var top = s[L - 1], k = 1;
      while (k < L && s[L - 1 - k] === top) k++;     // size of the top block
      var uniform = (k === L);
      if (uniform && L === cap) continue;            // complete tube: leave it
      for (var j = 0; j < tubes.length; j++) {
        if (j === i) continue;
        var d = tubes[j], free = cap - d.length;
        if (free <= 0) continue;                     // no room
        if (d.length === 0) { if (uniform) continue; }   // pointless shuffle
        else if (d[d.length - 1] !== top) continue;      // colors differ
        moves.push([i, j, k < free ? k : free]);
      }
    }
    return moves;
  }

  function apply(tubes, m) {
    var ns = tubes.slice(), s = tubes[m[0]], top = s[s.length - 1], add = '';
    for (var q = 0; q < m[2]; q++) add += top;
    ns[m[0]] = s.slice(0, s.length - m[2]);
    ns[m[1]] = tubes[m[1]] + add;
    return ns;
  }

  // BFS bookkeeping. states[i] = tubes joined by "|" (original tube order).
  var states = [startTubes.join('|')];
  var parent = [-1];          // index of the state we came from
  var packed = [0];           // the move that led here: from*1024 + to*32 + count
  var seen = new Set();
  seen.add(canonKey(startTubes));
  var head = 0, depth = 0, levelEnd = 1;

  function finish(idx) {
    var chain = [];
    for (var i = idx; parent[i] !== -1; i = parent[i]) chain.push(packed[i]);
    chain.reverse();
    var cur = startTubes.slice(), moves = [];
    for (var n = 0; n < chain.length; n++) {
      var p = chain[n];
      var m = [(p >> 10), ((p >> 5) & 31), (p & 31)];
      var s = cur[m[0]];
      moves.push({ from: m[0], to: m[1], count: m[2], color: s[s.length - 1] });
      cur = apply(cur, m);
    }
    return { done: true, found: true, moves: moves, explored: head };
  }

  /* Expand up to `budget` states. Returns {done:false,...} to be called
     again, or a final result {done:true, found, moves | reason}. */
  function step(budget) {
    if (isGoal(startTubes)) return { done: true, found: true, moves: [], explored: 0 };
    var spent = 0;
    while (head < states.length && spent < budget) {
      if (states.length > limit) return { done: true, found: false, reason: 'limit', explored: head };
      if (head === levelEnd) { depth++; levelEnd = states.length; }
      var tubes = states[head].split('|');
      var moves = genMoves(tubes);
      for (var q = 0; q < moves.length; q++) {
        var m = moves[q];
        var ns = apply(tubes, m);
        var key = canonKey(ns);
        if (seen.has(key)) continue;
        seen.add(key);
        states.push(ns.join('|'));
        parent.push(head);
        packed.push(m[0] * 1024 + m[1] * 32 + m[2]);
        if (isGoal(ns)) return finish(states.length - 1);
      }
      head++; spent++;
    }
    if (head >= states.length) return { done: true, found: false, reason: 'exhausted', explored: head };
    return { done: false, explored: head, queued: states.length - head, depth: depth };
  }

  return { step: step };
}

/* ---------------------------------------------------------------------
   3. VERIFIER  (independent of the solver: shares no code with it)

   Replays the moves from the ORIGINAL board with strict rule checks.
   Returns { ok, error, snaps } where snaps[k] is the board after k moves.
   Tubes here are arrays of color ids, bottom -> top.
   --------------------------------------------------------------------- */
function verifySolution(initialTubes, cap, moves) {
  function fail(msg) { return { ok: false, error: msg, snaps: null }; }
  function complete(tube) {
    if (tube.length !== cap) return false;
    return tube.every(function (c) { return c === tube[0]; });
  }
  var tubes = initialTubes.map(function (t) { return t.slice(); });
  var snaps = [tubes.map(function (t) { return t.slice(); })];

  var countBefore = {};
  tubes.forEach(function (t) { t.forEach(function (c) { countBefore[c] = (countBefore[c] || 0) + 1; }); });

  for (var k = 0; k < moves.length; k++) {
    var mv = moves[k], tag = 'Move ' + (k + 1) + ': ';
    if (!Number.isInteger(mv.from) || !Number.isInteger(mv.to) ||
        mv.from < 0 || mv.to < 0 || mv.from >= tubes.length || mv.to >= tubes.length) return fail(tag + 'tube out of range');
    if (mv.from === mv.to) return fail(tag + 'source and destination are the same');
    var src = tubes[mv.from], dst = tubes[mv.to];
    if (src.length === 0) return fail(tag + 'source tube is empty');
    if (complete(src)) return fail(tag + 'source tube is already complete');
    var top = src[src.length - 1], block = 0;
    for (var i = src.length - 1; i >= 0 && src[i] === top; i--) block++;
    var free = cap - dst.length;
    if (free <= 0) return fail(tag + 'destination is full');
    if (dst.length > 0 && dst[dst.length - 1] !== top) return fail(tag + 'colors do not match');
    if (dst.length === 0 && block === src.length) return fail(tag + 'pointless move into an empty tube');
    var amount = Math.min(block, free);
    if (amount !== mv.count) return fail(tag + 'wrong layer count');
    if (top !== mv.colorId) return fail(tag + 'wrong color');
    for (var n = 0; n < amount; n++) dst.push(src.pop());
    snaps.push(tubes.map(function (t) { return t.slice(); }));
  }

  // Layers must be conserved.
  var countAfter = {};
  tubes.forEach(function (t) { t.forEach(function (c) { countAfter[c] = (countAfter[c] || 0) + 1; }); });
  for (var c in countBefore) if (countBefore[c] !== countAfter[c]) return fail('Layers were lost or created');

  // Goal: every tube empty or completely full of one color.
  for (var t = 0; t < tubes.length; t++) {
    if (tubes[t].length !== 0 && !complete(tubes[t])) return fail('Final board is not solved (tube ' + (t + 1) + ')');
  }
  return { ok: true, error: null, snaps: snaps };
}

/* ---------------------------------------------------------------------
   4. RUNNER  (Web Worker, with a main-thread fallback)

   The worker source is built from makeSolver.toString(), so no separate
   worker file is needed. That also makes it work when index.html is
   opened straight from disk (file://), where external worker files are
   often blocked.
   --------------------------------------------------------------------- */
function runSolver(tubeStrings, cap, limit, onProgress) {
  var cancelled = false, worker = null, timer = null, blobUrl = null;

  var promise = new Promise(function (resolve) {
    function fallback() {
      var solver = makeSolver(tubeStrings, cap, limit);
      (function tick() {
        if (cancelled) return;
        var r = solver.step(2000);
        if (r.done) return resolve(r);
        if (onProgress) onProgress(r);
        timer = setTimeout(tick, 0);
      })();
    }
    try {
      var src = makeSolver.toString() + '\n' +
        'self.onmessage = function (e) {\n' +
        '  var d = e.data, s = makeSolver(d.tubes, d.cap, d.limit), r;\n' +
        '  do { r = s.step(25000); if (!r.done) postMessage({ type: "progress", r: r }); } while (!r.done);\n' +
        '  postMessage({ type: "done", r: r });\n' +
        '};';
      blobUrl = URL.createObjectURL(new Blob([src], { type: 'text/javascript' }));
      worker = new Worker(blobUrl);
      worker.onmessage = function (e) {
        if (e.data.type === 'progress') { if (onProgress) onProgress(e.data.r); }
        else { cleanup(); resolve(e.data.r); }
      };
      worker.onerror = function () { cleanup(); fallback(); };
      worker.postMessage({ tubes: tubeStrings, cap: cap, limit: limit });
    } catch (err) {
      cleanup();
      fallback();
    }
    function cleanup() {
      if (worker) { worker.terminate(); worker = null; }
      if (blobUrl) { URL.revokeObjectURL(blobUrl); blobUrl = null; }
    }
  });

  return {
    promise: promise,
    cancel: function () {
      cancelled = true;
      if (worker) { worker.terminate(); worker = null; }
      if (blobUrl) { URL.revokeObjectURL(blobUrl); blobUrl = null; }
      clearTimeout(timer);
    }
  };
}

/* Shared helper: solve + verify + decode. Used by the UI and the self-test.
   tubes: arrays of color ids, bottom -> top (extra empty tubes already added).
   Resolves to { status: 'solved', moves, snaps, explored }
              | { status: 'unsolvable' | 'limit' | 'invalid' | 'cancelled', ... } */
function solvePuzzle(tubes, cap, limit, onProgress) {
  var ids = [];
  tubes.forEach(function (t) { t.forEach(function (c) { if (ids.indexOf(c) < 0) ids.push(c); }); });
  var strs = tubes.map(function (t) {
    return t.map(function (c) { return String.fromCharCode(48 + ids.indexOf(c)); }).join('');
  });
  var job = runSolver(strs, cap, limit, onProgress);
  var p = job.promise.then(function (r) {
    if (r.cancelled) return { status: 'cancelled' };
    if (!r.found) return { status: r.reason === 'limit' ? 'limit' : 'unsolvable', explored: r.explored };
    var moves = r.moves.map(function (m) {
      return { from: m.from, to: m.to, count: m.count, colorId: ids[m.color.charCodeAt(0) - 48] };
    });
    var v = verifySolution(tubes, cap, moves);
    if (!v.ok) return { status: 'invalid', error: v.error };
    return { status: 'solved', moves: moves, snaps: v.snaps, explored: r.explored };
  });
  return { promise: p, cancel: job.cancel };
}

/* Node export (used only by the offline test script). */
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { makeSolver: makeSolver, verifySolution: verifySolution, EXAMPLES: EXAMPLES,
                     exampleToTubes: exampleToTubes, DEFAULT_PALETTE: DEFAULT_PALETTE };
}

/* ---------------------------------------------------------------------
   5. APP / UI
   --------------------------------------------------------------------- */
(function () {
  if (typeof document === 'undefined') return;

  var STORE_KEY = 'water-sort-solver-v1';
  var STATE_LIMIT = 2500000;
  var MAX_COLORS = 26;
  var EXTRA_HEX = ['#00b3a4', '#8b5a2b', '#9aa0a6', '#b6e63a', '#d81b60', '#283593', '#ffffff', '#3b3b3b'];
  var reduceMotion = window.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches;

  function $(id) { return document.getElementById(id); }
  function esc(s) {
    return String(s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }
  function clampInt(v, min, max, def) {
    var n = parseInt(v, 10);
    if (isNaN(n)) return def;
    return Math.max(min, Math.min(max, n));
  }
  function fmt(n) { return Number(n).toLocaleString(); }
  function textColor(hex) {
    var r = parseInt(hex.substr(1, 2), 16), g = parseInt(hex.substr(3, 2), 16), b = parseInt(hex.substr(5, 2), 16);
    return (0.299 * r + 0.587 * g + 0.114 * b) > 150 ? '#10131a' : '#ffffff';
  }

  /* ----- state ----- */
  var S;                 // the saved setup
  var sel = null;        // selected slot {t, l}
  var fast = false;      // "fill by tapping" mode
  var brush = null;      // color id | 'erase' | null
  var palById = {}, symbols = {};

  function emptyTubes(count, cap) {
    var a = [];
    for (var i = 0; i < count; i++) a.push(new Array(cap).fill(null));
    return a;
  }
  function blankState() {
    return { tubeCount: 10, cap: 4, palette: DEFAULT_PALETTE.map(function (c) { return { id: c.id, name: c.name, hex: c.hex }; }),
             tubes: emptyTubes(10, 4), colorblind: false, perRow: 0, speed: 6 };
  }
  function stateFromExample(ex) {
    var st = blankState(), tubes = exampleToTubes(ex);
    st.cap = 4; st.tubeCount = tubes.length;
    st.tubes = tubes.map(function (t) { var a = new Array(4).fill(null); t.forEach(function (c, i) { a[i] = c; }); return a; });
    return st;
  }

  /* Validate + clean an untrusted setup object (from localStorage or an import). */
  function sanitize(o) {
    if (!o || typeof o !== 'object') throw new Error('Not a setup object');
    var cap = clampInt(o.cap, 2, 8, 4), tc = clampInt(o.tubeCount, 2, 20, 10);
    if (!Array.isArray(o.palette) || !o.palette.length || o.palette.length > MAX_COLORS) throw new Error('Palette is missing or invalid');
    var ids = {};
    var palette = o.palette.map(function (p) {
      if (!p || !Number.isInteger(p.id) || ids[p.id] || !/^#[0-9a-f]{6}$/i.test(p.hex)) throw new Error('Palette entry is invalid');
      ids[p.id] = true;
      return { id: p.id, name: String(p.name || 'color').slice(0, 14), hex: p.hex.toLowerCase() };
    });
    var tubes = [];
    for (var t = 0; t < tc; t++) {
      var src = (Array.isArray(o.tubes) && Array.isArray(o.tubes[t])) ? o.tubes[t] : [], arr = new Array(cap).fill(null);
      for (var l = 0; l < cap; l++) arr[l] = (Number.isInteger(src[l]) && ids[src[l]]) ? src[l] : null;
      tubes.push(arr);
    }
    return { tubeCount: tc, cap: cap, palette: palette, tubes: tubes, colorblind: !!o.colorblind,
             perRow: clampInt(o.perRow, 0, 10, 0), speed: clampInt(o.speed, 1, 10, 6) };
  }

  function save() {
    try { localStorage.setItem(STORE_KEY, JSON.stringify(S)); } catch (e) { /* storage may be blocked */ }
  }
  function loadSaved() {
    try {
      var raw = localStorage.getItem(STORE_KEY);
      return raw ? sanitize(JSON.parse(raw)) : null;
    } catch (e) { return null; }
  }

  /* ----- lookups ----- */
  function buildSymbols(palette) {
    var used = {}, out = {}, fallback = '123456789#*+=?'.split('');
    palette.forEach(function (c) {
      var sym = null, name = c.name.toUpperCase();
      for (var i = 0; i < name.length; i++) {
        var ch = name[i];
        if (/[A-Z0-9]/.test(ch) && !used[ch]) { sym = ch; break; }
      }
      if (!sym) sym = fallback.filter(function (x) { return !used[x]; })[0] || '?';
      used[sym] = true; out[c.id] = sym;
    });
    return out;
  }
  function refreshLookups() {
    palById = {};
    S.palette.forEach(function (c) { palById[c.id] = c; });
    symbols = buildSymbols(S.palette);
  }

  /* ----- rendering: tubes ----- */
  /* tubes: arrays bottom -> top (entries may be null/undefined = empty).
     The DOM lists slots top -> bottom, so the top of the tube is on top. */
  function tubesHTML(tubes, cap, o) {
    var h = '';
    for (var t = 0; t < tubes.length; t++) {
      var arr = tubes[t], cls = 'tw';
      if (o.from === t) cls += ' from';
      if (o.to === t) cls += ' to';
      if (o.sel && o.sel.t === t) cls += ' active';
      var slots = '';
      for (var l = cap - 1; l >= 0; l--) {
        var id = arr[l], c = 'slot', style = '', sym = '';
        if (id !== null && id !== undefined && palById[id]) {
          var col = palById[id];
          c += ' f';
          style = 'background:' + col.hex + ';color:' + textColor(col.hex);
          if (S.colorblind) sym = esc(symbols[id]);
        }
        if (o.sel && o.sel.t === t && o.sel.l === l) c += ' sel';
        if (o.fresh && o.fresh.t === t && l >= o.fresh.from && l < o.fresh.from + o.fresh.count) c += ' new';
        slots += '<div class="' + c + '" data-t="' + t + '" data-l="' + l + '" style="' + style + '">' + sym + '</div>';
      }
      var tag = o.from === t ? 'from' : (o.to === t ? 'to' : '');
      h += '<div class="' + cls + '" data-t="' + t + '"><div class="tube">' + slots + '</div>' +
           '<div class="num" data-t="' + t + '">' + (t + 1) + '</div><div class="tag">' + tag + '</div></div>';
    }
    return h;
  }
  /* Layout: "Auto" splits the tubes into two rows, the top row getting the
     extra tube when the count is odd (10 -> 5+5, 9 -> 5+4, 8 -> 4+4).
     A fixed "Tubes per row" value overrides this. */
  function layoutGrid(el, cap, count) {
    var cols = S.perRow > 0 ? S.perRow : Math.ceil(count / 2);
    el.style.setProperty('--sh', (cap <= 4 ? 34 : cap <= 6 ? 28 : 23) + 'px');
    el.style.gridTemplateColumns = 'repeat(' + Math.max(1, cols) + ', minmax(0, 1fr))';
    // Keep tubes close together on wide screens (laptops); full width on phones.
    el.style.maxWidth = Math.max(1, cols) * 76 + 'px';
  }

  function renderBoard() {
    var el = $('board');
    layoutGrid(el, S.cap, S.tubeCount);
    el.innerHTML = tubesHTML(S.tubes, S.cap, { sel: sel });
    $('clearTube').disabled = !sel;
    $('fastBtn').setAttribute('aria-pressed', fast ? 'true' : 'false');
    $('hint').textContent = fast
      ? 'Pick a color, then tap slots to paint them. Tap a painted slot of the same color to erase it.'
      : (sel ? 'Slot selected in tube ' + (sel.t + 1) + '. Tap a color: it fills bottom to top, then moves to the next tube.'
             : 'Tap a slot (or a tube number), then tap a color.');
  }

  function renderChips() {
    var counts = {};
    S.tubes.forEach(function (a) { a.forEach(function (id) { if (id !== null) counts[id] = (counts[id] || 0) + 1; }); });
    var h = '';
    S.palette.forEach(function (c) {
      var on = fast && brush === c.id;
      h += '<button type="button" class="chip' + (on ? ' on' : '') + '" data-id="' + c.id + '" aria-label="' + esc(c.name) + '">' +
           '<span class="sw" style="background:' + c.hex + ';color:' + textColor(c.hex) + '">' + (S.colorblind ? esc(symbols[c.id]) : '') + '</span>' +
           '<span class="cn">' + (counts[c.id] || 0) + '/' + S.cap + '</span></button>';
    });
    h += '<button type="button" class="chip eraser' + (fast && brush === 'erase' ? ' on' : '') + '" data-id="erase" aria-label="Eraser">' +
         '<span class="sw">⌫</span><span class="cn">erase</span></button>';
    $('chips').innerHTML = h;
  }

  function renderEditor() {
    $('editorRows').innerHTML = S.palette.map(function (c) {
      return '<div class="prow" data-id="' + c.id + '">' +
        '<input type="color" class="pcol" value="' + c.hex + '" aria-label="Color for ' + esc(c.name) + '">' +
        '<input type="text" class="pname" maxlength="14" value="' + esc(c.name) + '" aria-label="Color name" autocomplete="off" spellcheck="false">' +
        '<button type="button" class="x" aria-label="Remove ' + esc(c.name) + '">×</button></div>';
    }).join('');
    $('editorSummary').textContent = 'Palette (' + S.palette.length + ' colors)';
  }

  function renderFields() {
    $('tubeCount').value = S.tubeCount;
    $('cap').value = S.cap;
    $('perRow').value = String(S.perRow);
    $('cb').checked = S.colorblind;
    $('speed').value = S.speed;
  }

  /* ----- validation ----- */
  function validate() {
    var counts = {}, gaps = [], filled = 0;
    S.palette.forEach(function (c) { counts[c.id] = 0; });
    S.tubes.forEach(function (arr, t) {
      var sawEmpty = false, gap = false;
      for (var l = 0; l < S.cap; l++) {
        if (arr[l] === null) sawEmpty = true;
        else { filled++; counts[arr[l]]++; if (sawEmpty) gap = true; }
      }
      if (gap) gaps.push(t);
    });
    var errors = [];
    if (!filled) errors.push('The board is empty. Paint some layers first.');
    gaps.forEach(function (t) { errors.push('Tube ' + (t + 1) + ' has an empty slot under a filled layer. Layers fill from the bottom.'); });
    var rows = S.palette.map(function (c) {
      var n = counts[c.id];
      return { c: c, n: n, state: n === 0 ? 'unused' : (n === S.cap ? 'ok' : 'bad') };
    });
    rows.forEach(function (r) {
      if (r.state === 'bad') errors.push(r.c.name + ' appears ' + r.n + ' of ' + S.cap + ' times. Each color needs exactly ' + S.cap + '.');
    });
    return { errors: errors, rows: rows };
  }

  function renderValidation() {
    var v = validate(), h = '<ul class="counts">';
    v.rows.forEach(function (r) {
      var icon = r.state === 'ok' ? '✓' : (r.state === 'bad' ? '!' : '–');
      h += '<li class="' + r.state + '"><span class="dot" style="background:' + r.c.hex + '"></span>' +
           esc(r.c.name) + ': ' + r.n + '/' + S.cap + ' <b>' + icon + '</b></li>';
    });
    h += '</ul>';
    if (v.errors.length) {
      h += '<ul class="errs">' + v.errors.map(function (e) { return '<li>' + esc(e) + '</li>'; }).join('') + '</ul>';
    } else {
      h += '<p class="okmsg">Board looks complete. Ready to solve.</p>';
    }
    h += '<p class="tip">Double-check look-alike shades: blue and lightblue, pink and purple, red and orange.</p>';
    $('validation').innerHTML = h;
    $('validation').className = 'valid ' + (v.errors.length ? 'has-errors' : 'all-ok');
    return v;
  }

  function renderSetup() {
    refreshLookups();
    renderFields(); renderEditor(); renderChips(); renderBoard(); renderValidation();
  }
  function afterEdit() {
    save(); invalidateResult();
    refreshLookups(); renderChips(); renderBoard(); renderValidation();
  }

  /* ----- toast ----- */
  var toastTimer = null;
  function toast(msg) {
    var t = $('toast');
    t.textContent = msg; t.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { t.classList.remove('show'); }, 2600);
  }

  /* ----- setup controls ----- */
  function setTubeCount(n) {
    n = clampInt(n, 2, 20, S.tubeCount);
    while (S.tubes.length < n) S.tubes.push(new Array(S.cap).fill(null));
    S.tubes.length = n; S.tubeCount = n;
    if (sel && sel.t >= n) sel = null;
    $('tubeCount').value = n; afterEdit();
  }
  function setCap(n) {
    n = clampInt(n, 2, 8, S.cap);
    var lost = false;
    S.tubes = S.tubes.map(function (arr) {
      var a = new Array(n).fill(null);
      for (var i = 0; i < arr.length; i++) { if (i < n) a[i] = arr[i]; else if (arr[i] !== null) lost = true; }
      return a;
    });
    S.cap = n;
    if (sel && sel.l >= n) sel = null;
    $('cap').value = n; afterEdit();
    if (lost) toast('Layers above the new capacity were removed.');
  }

  document.addEventListener('click', function (e) {
    var b = e.target.closest ? e.target.closest('[data-step]') : null;
    if (!b) return;
    var d = parseInt(b.getAttribute('data-d'), 10);
    if (b.getAttribute('data-step') === 'tubeCount') setTubeCount(S.tubeCount + d);
    else setCap(S.cap + d);
  });
  $('tubeCount').addEventListener('change', function () { setTubeCount(this.value); });
  $('cap').addEventListener('change', function () { setCap(this.value); });
  $('perRow').addEventListener('change', function () { S.perRow = clampInt(this.value, 0, 10, 0); save(); renderBoard(); if (P) renderPlayer(); });
  $('cb').addEventListener('change', function () {
    S.colorblind = this.checked; save(); renderChips(); renderBoard(); if (P) renderPlayer();
  });

  /* ----- painting ----- */
  function paintSlot(t, l, id) { S.tubes[t][l] = id; afterEdit(); }

  $('board').addEventListener('click', function (e) {
    var slot = e.target.closest('.slot'), num = e.target.closest('.num');
    if (slot) {
      var t = +slot.getAttribute('data-t'), l = +slot.getAttribute('data-l');
      if (fast) {
        if (brush === null) return toast('Pick a color first.');
        if (brush === 'erase') paintSlot(t, l, null);
        else paintSlot(t, l, S.tubes[t][l] === brush ? null : brush);
      } else {
        sel = (sel && sel.t === t && sel.l === l) ? null : { t: t, l: l };
        renderBoard();
      }
    } else if (num && !fast) {
      var tt = +num.getAttribute('data-t'), arr = S.tubes[tt], next = arr.indexOf(null);
      sel = { t: tt, l: next < 0 ? S.cap - 1 : next };
      renderBoard();
    }
  });

  $('chips').addEventListener('click', function (e) {
    var chip = e.target.closest('.chip');
    if (!chip) return;
    var raw = chip.getAttribute('data-id'), id = raw === 'erase' ? 'erase' : +raw;
    if (fast) { brush = id; renderChips(); return; }
    if (!sel) return toast('Tap a tube slot first, then a color.');
    var t = sel.t, l = sel.l;
    S.tubes[t][l] = id === 'erase' ? null : id;
    // Auto-advance: up the tube, then to the bottom of the next tube.
    if (l + 1 < S.cap) sel = { t: t, l: l + 1 };
    else if (t + 1 < S.tubeCount) {
      var nl = S.tubes[t + 1].indexOf(null);
      sel = { t: t + 1, l: nl < 0 ? 0 : nl };
    } else sel = null;
    afterEdit();
    var act = sel && $('board').querySelector('.tw.active');
    if (act && act.scrollIntoView) act.scrollIntoView({ block: 'nearest', behavior: reduceMotion ? 'auto' : 'smooth' });
  });

  $('fastBtn').addEventListener('click', function () {
    fast = !fast; sel = null; brush = null; renderChips(); renderBoard();
  });
  $('clearTube').addEventListener('click', function () {
    if (!sel) return;
    S.tubes[sel.t] = new Array(S.cap).fill(null);
    afterEdit();
  });
  $('clearAll').addEventListener('click', function () {
    if (!confirm('Empty every tube?')) return;
    S.tubes = emptyTubes(S.tubeCount, S.cap); sel = null; afterEdit();
  });

  /* ----- palette editor ----- */
  function colorUsed(id) {
    return S.tubes.some(function (a) { return a.indexOf(id) >= 0; });
  }
  $('editorRows').addEventListener('input', function (e) {
    var row = e.target.closest('.prow');
    if (!row) return;
    var c = palById[+row.getAttribute('data-id')];
    if (!c) return;
    if (e.target.classList.contains('pcol')) c.hex = e.target.value.toLowerCase();
    else if (e.target.classList.contains('pname')) c.name = e.target.value.trim().slice(0, 14) || 'color';
    afterEdit();
  });
  $('editorRows').addEventListener('click', function (e) {
    var x = e.target.closest('.x');
    if (!x) return;
    var id = +x.parentNode.getAttribute('data-id');
    if (S.palette.length <= 1) return toast('Keep at least one color.');
    if (colorUsed(id) && !confirm('This color is on the board. Remove it and clear its layers?')) return;
    S.palette = S.palette.filter(function (c) { return c.id !== id; });
    S.tubes = S.tubes.map(function (a) { return a.map(function (v) { return v === id ? null : v; }); });
    if (brush === id) brush = null;
    refreshLookups(); renderEditor(); afterEdit();
  });
  $('addColor').addEventListener('click', function () {
    if (S.palette.length >= MAX_COLORS) return toast('Maximum ' + MAX_COLORS + ' colors.');
    var nextId = S.palette.reduce(function (m, c) { return Math.max(m, c.id); }, -1) + 1;
    S.palette.push({ id: nextId, name: 'color ' + (S.palette.length + 1), hex: EXTRA_HEX[S.palette.length % EXTRA_HEX.length] });
    refreshLookups(); renderEditor(); afterEdit();
    var rows = $('editorRows').querySelectorAll('.pname');
    if (rows.length) rows[rows.length - 1].focus();
  });

  /* ----- examples, export / import, reset ----- */
  function boardHasLayers() {
    return S.tubes.some(function (a) { return a.some(function (v) { return v !== null; }); });
  }
  $('example').addEventListener('change', function () {
    var ex = EXAMPLES.filter(function (x) { return x.key === $('example').value; })[0];
    $('example').value = '';
    if (!ex) return;
    if (boardHasLayers() && !confirm('Replace the current board and palette with ' + ex.name + '?')) return;
    var keep = { colorblind: S.colorblind, perRow: S.perRow, speed: S.speed };
    S = stateFromExample(ex);
    S.colorblind = keep.colorblind; S.perRow = keep.perRow; S.speed = keep.speed;
    sel = null; brush = null; save(); invalidateResult(); renderSetup();
    toast(ex.name + ' loaded.');
  });

  $('exportBtn').addEventListener('click', function () {
    var json = JSON.stringify(S, null, 1);
    $('backupText').value = json;
    try {
      var url = URL.createObjectURL(new Blob([json], { type: 'application/json' }));
      var a = document.createElement('a');
      a.href = url; a.download = 'water-sort-setup.json';
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
    } catch (err) { /* the text box still holds the JSON */ }
    toast('Setup exported.');
  });
  function importText(text) {
    try {
      S = sanitize(JSON.parse(text));
      sel = null; brush = null; save(); invalidateResult(); renderSetup();
      toast('Setup imported.');
    } catch (err) { toast('Import failed: ' + err.message); }
  }
  $('importTextBtn').addEventListener('click', function () { importText($('backupText').value); });
  $('importFile').addEventListener('change', function () {
    var f = this.files && this.files[0];
    if (!f) return;
    var r = new FileReader();
    r.onload = function () { importText(String(r.result)); };
    r.readAsText(f);
    this.value = '';
  });
  $('resetBtn').addEventListener('click', function () {
    if (!confirm('Reset everything to the default empty board?')) return;
    S = blankState(); sel = null; brush = null; fast = false;
    save(); invalidateResult(); renderSetup();
    toast('Reset.');
  });

  /* ================================================================
     History: every Start press is logged, with its result when known
     ================================================================ */
  var HIST_KEY = 'water-sort-solver-history-v1', HIST_MAX = 50;
  var H = [], curHist = null;

  function loadHistory() {
    try {
      var a = JSON.parse(localStorage.getItem(HIST_KEY));
      if (!Array.isArray(a)) return [];
      return a.filter(function (e) { return e && e.id && e.setup && e.status; }).map(function (e) {
        if (e.status === 'solving') e.status = 'interrupted';   // page was closed mid-search
        return e;
      }).slice(0, HIST_MAX);
    } catch (e) { return []; }
  }
  function saveHistory() {
    try { localStorage.setItem(HIST_KEY, JSON.stringify(H)); } catch (e) { /* storage may be blocked */ }
  }
  function addHistory(extra) {
    var e = {
      id: Date.now().toString(36) + Math.random().toString(36).slice(2, 6),
      time: new Date().toISOString(),
      status: 'solving',
      extraTubes: extra,
      // Same shape as an exported setup, so it can be imported back as-is.
      setup: { tubeCount: S.tubeCount, cap: S.cap, palette: JSON.parse(JSON.stringify(S.palette)), tubes: JSON.parse(JSON.stringify(S.tubes)) },
      moveCount: null, moves: null, seconds: null, statesChecked: null
    };
    H.unshift(e);
    if (H.length > HIST_MAX) H.length = HIST_MAX;
    saveHistory(); renderHistory();
    return e.id;
  }
  function updateHistory(id, patch) {
    for (var i = 0; i < H.length; i++) {
      if (H[i].id === id) { for (var k in patch) H[i][k] = patch[k]; break; }
    }
    saveHistory(); renderHistory();
  }
  function historyMoves(moves, palette) {
    var names = {};
    palette.forEach(function (c) { names[c.id] = c.name; });
    return moves.map(function (m, i) {
      return { step: i + 1, from: m.from + 1, to: m.to + 1, layers: m.count, color: names[m.colorId] || String(m.colorId) };
    });
  }
  var STATUS_TEXT = { solving: 'Solving…', solved: 'Solved', unsolvable: 'No solution', limit: 'Search too large',
                      cancelled: 'Cancelled', interrupted: 'Interrupted', error: 'Check failed' };
  function renderHistory() {
    var box = $('historyList');
    if (!H.length) { box.innerHTML = '<p class="tip">Nothing yet. Each time you press Start, the board is logged here.</p>'; }
    else {
      box.innerHTML = H.map(function (e) {
        var label = STATUS_TEXT[e.status] || e.status;
        if (e.status === 'solved') label += ' in ' + e.moveCount + ' move' + (e.moveCount === 1 ? '' : 's');
        var extra = e.extraTubes ? ' + ' + e.extraTubes + ' extra tube' + (e.extraTubes === 1 ? '' : 's') : '';
        return '<div class="hrow ' + esc(e.status) + '" data-id="' + esc(e.id) + '">' +
          '<div class="hinfo"><div class="hstatus">' + esc(label) + '</div>' +
          '<div class="hmeta">' + esc(new Date(e.time).toLocaleString()) + '<br>' + e.setup.tubeCount + ' tubes' + extra + ', ' + e.setup.cap + ' layers</div></div>' +
          '<div class="hbtns"><button type="button" class="btn sm" data-act="load">Load</button>' +
          '<button type="button" class="btn sm" data-act="export">Export</button>' +
          '<button type="button" class="btn sm danger" data-act="del" aria-label="Delete entry">×</button></div></div>';
      }).join('');
    }
    $('histExportAll').disabled = !H.length;
    $('histClear').disabled = !H.length;
  }
  function downloadJSON(filename, obj) {
    var json = JSON.stringify(obj, null, 1);
    try {
      var url = URL.createObjectURL(new Blob([json], { type: 'application/json' }));
      var a = document.createElement('a');
      a.href = url; a.download = filename;
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
    } catch (err) { toast('Download is not available in this browser.'); }
  }
  function stamp(e) { return e.time.slice(0, 19).replace(/[:T]/g, '-'); }

  $('historyList').addEventListener('click', function (e) {
    var b = e.target.closest('[data-act]');
    if (!b) return;
    var id = b.parentNode.parentNode.getAttribute('data-id');
    var entry = H.filter(function (x) { return x.id === id; })[0];
    if (!entry) return;
    var act = b.getAttribute('data-act');
    if (act === 'export') {
      downloadJSON('water-sort-' + stamp(entry) + '.json', { app: 'water-sort-solver', version: 1, exportedAt: new Date().toISOString(), entry: entry });
    } else if (act === 'del') {
      H = H.filter(function (x) { return x.id !== id; });
      saveHistory(); renderHistory();
    } else if (act === 'load') {
      if (boardHasLayers() && !confirm('Replace the current board with this entry?')) return;
      try {
        var o = JSON.parse(JSON.stringify(entry.setup));
        o.colorblind = S.colorblind; o.perRow = S.perRow; o.speed = S.speed;
        S = sanitize(o);
        sel = null; brush = null; save(); invalidateResult(); renderSetup();
        toast('Board loaded from history.');
        $('board').scrollIntoView({ behavior: reduceMotion ? 'auto' : 'smooth', block: 'start' });
      } catch (err) { toast('Could not load this entry.'); }
    }
  });
  $('histExportAll').addEventListener('click', function () {
    downloadJSON('water-sort-history.json', { app: 'water-sort-solver', version: 1, exportedAt: new Date().toISOString(), history: H });
  });
  $('histClear').addEventListener('click', function () {
    if (!confirm('Delete the whole history?')) return;
    H = []; saveHistory(); renderHistory();
  });

  /* ================================================================
     Solve flow
     ================================================================ */
  var job = null, lastExtra = 0, solving = false;

  function setSolving(on) {
    solving = on;
    $('solving').hidden = !on;
    $('startBtn').disabled = on;
  }

  function startSolve(extra) {
    var v = validate();
    if (v.errors.length) {
      toast('Fix the board first: ' + v.errors[0]);
      $('validation').scrollIntoView({ behavior: reduceMotion ? 'auto' : 'smooth', block: 'center' });
      return;
    }
    invalidateResult();
    var tubes = S.tubes.map(function (a) { return a.filter(function (x) { return x !== null; }); });
    for (var i = 0; i < extra; i++) tubes.push([]);
    lastExtra = extra;
    var histId = curHist = addHistory(extra);
    setSolving(true);
    $('progress').textContent = 'Starting…';
    $('solving').scrollIntoView({ behavior: reduceMotion ? 'auto' : 'smooth', block: 'center' });
    var t0 = Date.now(), cap = S.cap, base = S.tubeCount, palSnapshot = JSON.parse(JSON.stringify(S.palette));

    job = solvePuzzle(tubes, cap, STATE_LIMIT, function (r) {
      $('progress').textContent = 'Checked ' + fmt(r.explored) + ' states. Searching ' + r.depth + ' moves deep.';
    });
    var mine = job;
    job.promise.then(function (res) {
      if (job !== mine) return;
      job = null; setSolving(false);
      var secs = ((Date.now() - t0) / 1000).toFixed(1);
      if (res.status === 'cancelled') return updateHistory(histId, { status: 'cancelled' });
      if (res.status === 'solved') {
        updateHistory(histId, { status: 'solved', moveCount: res.moves.length, seconds: +secs, statesChecked: res.explored,
                                moves: historyMoves(res.moves, palSnapshot) });
        return showResult(tubes, cap, res, extra, base, secs);
      }
      updateHistory(histId, { status: res.status === 'invalid' ? 'error' : res.status, statesChecked: res.explored || null });
      showProblem(res);
    });
  }

  $('startBtn').addEventListener('click', function () { startSolve(0); });
  $('cancelBtn').addEventListener('click', function () {
    if (job) { job.cancel(); job = null; }
    if (curHist) updateHistory(curHist, { status: 'cancelled' });
    setSolving(false);
    toast('Search cancelled.');
  });

  function showProblem(res) {
    var box = $('problem'), h;
    if (res.status === 'unsolvable') {
      h = '<h2>No solution found</h2><p>All ' + fmt(res.explored) + ' reachable layouts were checked and none ends sorted.</p>' +
          '<ul><li>Re-check the colors. Look-alike shades are the usual cause (blue and lightblue, pink and purple, red and orange).</li>' +
          '<li>Make sure every tube matches the game, top to bottom.</li></ul>' +
          '<div class="row"><button type="button" class="btn" id="recheck">Re-check colors</button>' +
          '<button type="button" class="btn primary" id="plusOne">Try with +1 extra tube</button></div>';
    } else if (res.status === 'limit') {
      h = '<h2>Search too large</h2><p>The search passed ' + fmt(STATE_LIMIT) + ' states and was stopped to protect your device. ' +
          'Check the colors, or try again with an extra empty tube, which often makes puzzles much easier.</p>' +
          '<div class="row"><button type="button" class="btn" id="recheck">Re-check colors</button>' +
          '<button type="button" class="btn primary" id="plusOne">Try with +1 extra tube</button></div>';
    } else {
      h = '<h2>Internal check failed</h2><p>The solver produced moves that did not pass the strict replay check (' + esc(res.error || 'unknown') +
          '). No answer is shown, because it could be wrong. Please re-check the board.</p>';
    }
    box.innerHTML = h; box.hidden = false;
    box.scrollIntoView({ behavior: reduceMotion ? 'auto' : 'smooth', block: 'center' });
    var r = $('recheck'), p = $('plusOne');
    if (r) r.addEventListener('click', function () { $('board').scrollIntoView({ behavior: 'smooth', block: 'center' }); });
    if (p) p.addEventListener('click', function () { startSolve(lastExtra + 1); });
  }

  /* ================================================================
     Step-by-step player
     ================================================================ */
  var P = null;   // { moves, snaps, cap, n, s, playing, timer, busy }

  function invalidateResult() {
    if (P) stopPlay();
    P = null;
    $('result').hidden = true;
    $('problem').hidden = true;
    $('moveList').innerHTML = '';
  }

  function showResult(tubes, cap, res, extra, baseCount, secs) {
    P = { moves: res.moves, snaps: res.snaps, cap: cap, n: res.moves.length, s: 0, playing: false, timer: null, busy: false };
    var sum;
    if (P.n === 0) sum = 'The board is already solved. No moves needed.';
    else sum = 'Solved in ' + P.n + ' move' + (P.n === 1 ? '' : 's') + ' (shortest possible). Found in ' + secs + ' s after checking ' + fmt(res.explored) + ' states.';
    if (extra > 0) {
      var nums = [];
      for (var i = 0; i < extra; i++) nums.push(baseCount + i + 1);
      sum += ' This uses ' + extra + ' extra empty tube' + (extra === 1 ? '' : 's') + ' that you do not have yet (tube ' + nums.join(', ') + ').';
    }
    $('summary').textContent = sum;
    $('jump').max = Math.max(1, P.n); $('jump').value = 1;

    // Move list (built once, highlighted in renderPlayer)
    $('moveList').innerHTML = P.moves.map(function (m, i) {
      return '<button type="button" class="mv" data-i="' + i + '" aria-label="Step ' + (i + 1) + ': tube ' + (m.from + 1) + ' to tube ' + (m.to + 1) + '">' + (m.from + 1) + '→' + (m.to + 1) + '</button>';
    }).join('');

    $('result').hidden = false;
    renderPlayer();
    $('result').scrollIntoView({ behavior: reduceMotion ? 'auto' : 'smooth', block: 'start' });
  }

  function layersText(m) {
    var c = palById[m.colorId];
    return m.count + ' layer' + (m.count === 1 ? '' : 's') + ' of ' + (c ? esc(c.name) : '?');
  }

  /* Render step P.s: the board BEFORE move P.s, with that move's tubes highlighted. */
  function renderPlayer(fresh) {
    if (!P) return;
    var el = $('playBoard'), done = P.s >= P.n, m = done ? null : P.moves[P.s];
    layoutGrid(el, P.cap, P.snaps[0].length);
    el.innerHTML = tubesHTML(P.snaps[P.s], P.cap, { from: m ? m.from : -1, to: m ? m.to : -1, fresh: fresh });

    if (P.n === 0) $('stepText').innerHTML = 'Nothing to do. Every tube is already sorted.';
    else if (done) $('stepText').innerHTML = '<strong>Solved!</strong> Every tube is empty or full of one color.';
    else {
      var c = palById[m.colorId];
      $('stepText').innerHTML = 'Step ' + (P.s + 1) + ' of ' + P.n + ': pour <strong>tube ' + (m.from + 1) + ' → tube ' + (m.to + 1) +
        '</strong> (<span class="dot" style="background:' + (c ? c.hex : '#888') + '"></span>' + layersText(m) + ')';
    }

    $('prevBtn').disabled = P.s === 0;
    $('restartBtn').disabled = P.s === 0;
    $('nextBtn').disabled = done;
    $('playBtn').textContent = P.playing ? 'Pause' : 'Play';
    $('playBtn').setAttribute('aria-pressed', P.playing ? 'true' : 'false');
    $('playBtn').disabled = P.n === 0;
    if (!done) $('jump').value = P.s + 1;

    var list = $('moveList'), cur = null;
    Array.prototype.forEach.call(list.children, function (b, i) {
      b.classList.toggle('cur', i === P.s);
      b.classList.toggle('past', i < P.s);
      if (i === P.s) cur = b;
    });
    if (cur) list.scrollTop = Math.max(0, cur.offsetTop - list.clientHeight / 2 + cur.offsetHeight / 2);
  }

  function delayMs() { return 2600 - S.speed * 230; }

  /* Animate one move forward, then show the next step. */
  function stepForward(cb) {
    if (!P || P.busy || P.s >= P.n) { if (cb) cb(); return; }
    var m = P.moves[P.s], before = P.snaps[P.s][m.to].length;
    var finishStep = function () {
      P.s++; P.busy = false;
      renderPlayer({ t: m.to, from: before, count: m.count });
      if (cb) cb();
    };
    if (reduceMotion) { finishStep(); return; }
    P.busy = true;
    // phase 1: fade the poured layers out of the source tube
    var tops = $('playBoard').querySelectorAll('.slot.f[data-t="' + m.from + '"]');
    for (var i = 0; i < m.count && i < tops.length; i++) tops[i].classList.add('leaving');
    setTimeout(function () { if (P) finishStep(); }, Math.min(230, delayMs() * 0.6));
  }

  function stopPlay() {
    if (!P) return;
    P.playing = false;
    clearTimeout(P.timer);
  }
  function playTick() {
    if (!P || !P.playing) return;
    if (P.s >= P.n) { stopPlay(); renderPlayer(); return; }
    stepForward(function () {
      if (!P || !P.playing) return;
      if (P.s >= P.n) { stopPlay(); renderPlayer(); return; }
      P.timer = setTimeout(playTick, delayMs());
    });
  }

  function goto(s) {
    if (!P) return;
    stopPlay();
    P.busy = false;
    P.s = Math.max(0, Math.min(P.n, s));
    renderPlayer();
  }

  $('nextBtn').addEventListener('click', function () { if (!P) return; stopPlay(); stepForward(function () { renderPlayer(); }); });
  $('prevBtn').addEventListener('click', function () { if (P && !P.busy) goto(P.s - 1); });
  $('restartBtn').addEventListener('click', function () { goto(0); });
  $('playBtn').addEventListener('click', function () {
    if (!P || P.busy) return;
    if (P.playing) { stopPlay(); renderPlayer(); return; }
    if (P.s >= P.n) { P.s = 0; renderPlayer(); }
    P.playing = true; renderPlayer();
    P.timer = setTimeout(playTick, 250);
  });
  $('speed').addEventListener('input', function () { S.speed = clampInt(this.value, 1, 10, 6); save(); });
  $('jumpBtn').addEventListener('click', function () { goto(clampInt($('jump').value, 1, Math.max(1, P ? P.n : 1), 1) - 1); });
  $('jump').addEventListener('keydown', function (e) { if (e.key === 'Enter') $('jumpBtn').click(); });
  $('moveList').addEventListener('click', function (e) {
    var b = e.target.closest('.mv');
    if (b) goto(+b.getAttribute('data-i'));
  });

  /* ================================================================
     Hidden self-test (add ?test to the URL)
     ================================================================ */
  function runSelfTest() {
    var box = $('selftest');
    box.hidden = false;
    box.innerHTML = '<h2>Self-test</h2><ul id="stList"></ul><p id="stSummary" class="tip">Running…</p>';
    var list = $('stList'), passed = 0, idx = 0;
    (function next() {
      if (idx >= EXAMPLES.length) {
        $('stSummary').textContent = passed === EXAMPLES.length ? 'All ' + passed + ' tests passed.' : (EXAMPLES.length - passed) + ' test(s) failed.';
        return;
      }
      var ex = EXAMPLES[idx++], li = document.createElement('li');
      li.textContent = ex.name + ': running…'; list.appendChild(li);
      var t0 = Date.now(), tubes = exampleToTubes(ex);
      solvePuzzle(tubes, 4, STATE_LIMIT).promise.then(function (res) {
        var secs = ((Date.now() - t0) / 1000).toFixed(1);
        var ok = res.status === 'solved' && res.moves.length === ex.expected;
        if (ok) passed++;
        li.className = ok ? 'pass' : 'fail';
        li.textContent = (ok ? 'PASS ' : 'FAIL ') + ex.name + ': ' +
          (res.status === 'solved' ? res.moves.length + ' moves (expected ' + ex.expected + ')' : res.status + (res.error ? ' ' + res.error : '')) +
          ' in ' + secs + ' s';
        next();
      });
    })();
  }

  /* ================================================================
     Boot
     ================================================================ */
  var firstRun = false;
  S = loadSaved();
  if (!S) { S = stateFromExample(EXAMPLES[0]); firstRun = true; save(); }
  H = loadHistory();
  renderSetup();
  renderHistory();
  if (firstRun) toast('Level 27 is loaded as a demo. Press Start, or clear it and enter your own board.');
  if (/[?&]test\b/.test(location.search)) runSelfTest();
})();
