const express = require('express');
const bodyParser = require("body-parser");
const path = require('path');

process.on("uncaughtException", (err) => console.log("❌ Uncaught Exception:", err.message));
process.on("unhandledRejection", (err) => console.log("❌ Unhandled Rejection:", err?.message || err));

require('events').EventEmitter.defaultMaxListeners = 500;

const app = express();
const PORT = process.env.PORT || 5000;
const __path = process.cwd();

app.use(bodyParser.json());
app.use(bodyParser.urlencoded({ extended: true }));

app.use('/code', require('./pair'));
app.use('/pair', async (req, res) => res.sendFile(path.join(__path, 'pair.html')));
app.use('/', async (req, res) => res.sendFile(path.join(__path, 'main.html')));

app.listen(PORT, () => console.log(`🚀 Server running on http://localhost:${PORT}`));
