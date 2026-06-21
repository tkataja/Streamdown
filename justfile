set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

fork_url := "git+https://github.com/tkataja/Streamdown.git"

install:
    uv tool install --reinstall .

install-local: install

install-fork:
    uv tool install --upgrade {{fork_url}}
