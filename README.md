# Water Sort Solver

A static, fully offline solver for water sort puzzles. Three files, no build step, no frameworks, no backend, no network requests, no AI. The solver is a plain breadth-first search.

## Run it

Open `index.html` in any modern browser. That is all.

Add `?test` to the URL (for example `index.html?test`) to run the built-in self-test. It solves Levels 27, 28 and 29 and shows PASS or FAIL for each (expected 26, 22 and 24 moves).

## How to use

1. Set the number of tubes and layers per tube, and edit the palette so it matches your game.
2. Tap a slot (or a tube number), then tap a color. Or switch on "Fill by tapping", pick a color and tap slots.
3. Check the validation panel: each color must appear exactly as many times as the tube capacity.
4. Press Start. Follow the steps, or press Play.

Tubes are numbered left to right, row by row from the top. Use "Tubes per row" to match your game's layout.

## How the solver works

- Breadth-first search over board states, so the first solution found is the shortest.
- States are deduplicated with a canonical key: tubes sorted, colors renamed by first appearance. Tube order and color names do not matter.
- Moves pour the whole top block of one color, or only the part that fits. Never out of a complete tube, and never a uniform tube into an empty one.
- The search runs in a Web Worker (built from a Blob, so it also works from `file://`). If workers are unavailable it falls back to the main thread in small slices.
- Limit: 2.5 million states, then a clear message is shown.
- An independent replay verifier re-applies every move with strict checks. If the replay does not end solved, an error is shown instead of an answer.

## Deploy for free

**GitHub Pages**: push the three files to a repository, then Settings → Pages → deploy from the `main` branch, root folder.

**Cloudflare Pages**: create a project, connect the repository (or upload the folder directly), leave the build command empty and set the output directory to `/`.

Netlify Drop or any static host works the same way.
