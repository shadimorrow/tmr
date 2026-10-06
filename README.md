## Tehran Metro Route Finder

A simple Tehran Metro route finder built with React and Vite.

The project models metro stations as a graph and uses Dijkstra's algorithm to find the best route between stations. Changing metro lines adds an extra cost to the route, helping prioritize routes with fewer line changes.

Getting Started
```
npm install
npm run dev
```

For a production build:
```
npm run build
npm run preview
```

Project Structure:
- "src/main.jsx" — Map logic, graph model, and routing
- "src/styles.css" — UI and visual styling
- "index.html" — Metadata and application entry point

Data:
Map data is provided by OpenStreetMap, and station data comes from a public Tehran Metro dataset.

Attribution:
Developed by Shadi with assistance from OpenAI Codex.
