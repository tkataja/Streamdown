set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

fork_url := "git+https://github.com/tkataja/Streamdown.git"

install-fork:
    uv tool install --upgrade {{fork_url}}
