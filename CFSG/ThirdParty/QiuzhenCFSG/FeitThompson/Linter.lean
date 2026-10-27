module

public meta import Batteries.Tactic.Lint

namespace CFSG
end CFSG
open CFSG

public meta section

open Lean Meta

namespace CFSG.FeitThompson.Linter
open Batteries.Tactic.Lint

/-- Remove leading whitespace from a line. -/
def trimLeft (s : String) : String :=
  (s.dropWhile Char.isWhitespace).toString

/-- Return `true` iff a line begins with a Lean single-line or block comment delimiter. -/
def isCommentLine (s : String) : Bool :=
  let s := trimLeft s
  s.startsWith "--" || s.startsWith "/-"

/-- Heuristic detector for lines that contain an explicit `private` command modifier. -/
def lineHasPrivateModifierToken (line : String) : Bool :=
  let line := trimLeft line
  if isCommentLine line then
    false
  else
    line == "private" ||
      line.startsWith "private " ||
      (line.startsWith "@[" && line.contains " private ")

/-- Find the first line containing an explicit `private` command modifier. -/
def findPrivateCommandLine? (lines : Array String) : Option Nat := Id.run do
  let mut i := 0
  while h : i < lines.size do
    if lineHasPrivateModifierToken lines[i] then
      return some (i + 1)
    i := i + 1
  return none

/-- Find the first line containing `@[expose] public section` (possibly split across lines). -/
def findExposePublicSectionLine? (lines : Array String) : Option Nat := Id.run do
  let mut i := 0
  while h : i < lines.size do
    let line := trimLeft lines[i]
    if !isCommentLine line then
      if line.startsWith "@[expose] public section" then
        return some (i + 1)
      if line == "@[expose]" then
        let mut j := i + 1
        while h' : j < lines.size do
          let next := trimLeft lines[j]
          if next.isEmpty || isCommentLine next then
            j := j + 1
            continue
          if next.startsWith "public section" then
            return some (i + 1)
          break
    i := i + 1
  return none

/-- Pick a public declaration in `mod` to anchor a lint message for a command at `line`. -/
def anchorDeclForLine? (mod : Name) (line : Nat) : MetaM (Option Name) := do
  let pkgDecls ← getDeclsInPackage mod.getRoot
  let mut bestAfter : Option (Nat × Name) := none
  let mut bestAny : Option (Nat × Name) := none
  for declName in pkgDecls do
    if isPrivateName declName then
      continue
    let some declMod ← findModuleOf? declName | continue
    if declMod != mod then
      continue
    let some ranges ← findDeclarationRanges? declName | continue
    let declLine := ranges.range.pos.line
    match bestAny with
    | none => bestAny := some (declLine, declName)
    | some (bestLine, bestName) =>
      if declLine < bestLine || (declLine == bestLine && declName.lt bestName) then
        bestAny := some (declLine, declName)
    if declLine >= line then
      match bestAfter with
      | none => bestAfter := some (declLine, declName)
      | some (bestLine, bestName) =>
        if declLine < bestLine || (declLine == bestLine && declName.lt bestName) then
          bestAfter := some (declLine, declName)
  return (bestAfter <|> bestAny).map Prod.snd

/-- Load source lines for module `mod`, or return `#[]` if the source file cannot be read. -/
def getModuleLines (mod : Name) : MetaM (Array String) := do
  let srcSearchPath ← getSrcSearchPath
  let filePath := (← srcSearchPath.findWithExt "lean" mod).getD (modToFilePath "." mod "lean")
  let contents ← try
      IO.FS.readFile filePath
    catch _ =>
      pure ""
  pure <| (contents.splitOn "\n").toArray

/-- Batteries `lake lint` rule banning explicit `private ...` commands. -/
@[env_linter] public meta def banPrivateCommand : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No uses of `private ...` commands found."
  errorsFound := "BANNED `private ...` COMMANDS:"
  test declName := do
    if ← isAutoDecl declName then
      return none
    let mod ← match (← findModuleOf? declName) with
      | some mod => pure mod
      | none => pure (← getEnv).mainModule
    if mod.getRoot != `FeitThompson && mod.getRoot != `Tests then
      return none
    let lines ← getModuleLines mod
    let some line := findPrivateCommandLine? lines | return none
    let anchor := (← anchorDeclForLine? mod line).getD Name.anonymous
    if declName == anchor then
      return m!"`private ...` is banned in this project (line {line})"
    return none

/-- Batteries `lake lint` rule banning `@[expose] public section`. -/
@[env_linter] public meta def banExposePublicSection : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No uses of `@[expose] public section` found."
  errorsFound := "BANNED `@[expose] public section` COMMANDS:"
  test declName := do
    if ← isAutoDecl declName then
      return none
    let mod ← match (← findModuleOf? declName) with
      | some mod => pure mod
      | none => pure (← getEnv).mainModule
    if mod.getRoot != `FeitThompson && mod.getRoot != `Tests then
      return none
    let lines ← getModuleLines mod
    let some line := findExposePublicSectionLine? lines | return none
    if declName == (← anchorDeclForLine? mod line).getD Name.anonymous then
      return m!"`@[expose] public section` is banned in this project (line {line})"
    return none

end CFSG.FeitThompson.Linter
