module
public import CFSG.Sporadic.HNSchreier.KernelBytes
public meta import Lean.Elab.Term
public import Lean.Exception

public meta section
open Lean Elab Term

elab "include_hex_bytes% " path:str : term => do
  let file := ((System.FilePath.mk (← getFileName)).parent.getD ".") / path.getString
  let raw ← IO.FS.readBinFile file
  let mut bs := ByteArray.empty
  let mut body := false
  let mut hi : Option Nat := none
  for c in raw do
    if !body then
      if c == 10 then body := true
    else
      let n := c.toNat
      if (48 ≤ n && n < 58) || (97 ≤ n && n < 103) then
        let v := if n < 58 then n - 48 else n - 87
        match hi with
        | none => hi := some v
        | some h =>
          bs := bs.push (UInt8.ofNat (16 * h + v))
          hi := none
  if bs.isEmpty then throwError "empty hexadecimal archive"
  let width := 256
  let mut leaves : Array Expr := #[]
  for block in [:((bs.size + width - 1) / width)] do
    let start := block * width
    let len := min width (bs.size - start)
    let mut n := 0
    for j in [:len] do
      n := n + (bs[start + j]!.toNat <<< (8 * j))
    leaves := leaves.push (mkApp2 (Lean.mkConst ``CFSG.Sporadic.HNSchreier.KernelBytes.packed)
      (mkNatLit len) (mkNatLit n))
  let append := Lean.mkConst ``CFSG.Sporadic.HNSchreier.KernelBytes.appendSized
  let refl (n : Nat) := mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) (Lean.mkConst ``Nat) (mkNatLit n)
  let rec build (fuel lo hi : Nat) : StateM (Std.HashMap (Expr × Expr) Expr) Expr := do
    match fuel with
    | 0 => return leaves[lo]!
    | fuel + 1 =>
      if lo + 1 == hi then return leaves[lo]!
      let mid := (lo + hi) / 2
      let a ← build fuel lo mid
      let b ← build fuel mid hi
      if let some e := (← get)[(a, b)]? then return e
      let leftSize := min bs.size (mid * width) - lo * width
      let rightSize := min bs.size (hi * width) - mid * width
      let e := mkApp6 append (mkNatLit leftSize) (mkNatLit rightSize) a b (refl leftSize) (refl rightSize)
      modify (·.insert (a, b) e)
      return e
  let (e, finalCache) := (build leaves.size 0 leaves.size).run ∅
  logInfo m!"Included {bs.size} archive bytes in {leaves.size} packed leaves / {finalCache.size} distinct balanced branches"
  return e

end
