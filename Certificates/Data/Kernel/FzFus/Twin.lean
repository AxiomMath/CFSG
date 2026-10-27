module

public meta import Certificates.Data.Kernel.FzJt.Twin
public import Certificates.Data.Kernel.FzJt.Twin

namespace Certificates.FzFus.Twin

open CFSG.KC.Eval Certificates.FzJt.Twin

public meta def TT : Nat := 548990458703455256239736400950543188581013418660442459642934095276333109462153613769925705334784
public meta def REPT : Nat := 220860097234124997481754757498753492068537512105336813684345155494356041
public meta def mulR (c d : Nat) : Nat :=
  let a1 := c &&& 7; let b1 := (c >>> 3) &&& 7; let c1 := (c >>> 6) &&& 7; let e1 := c >>> 9
  let a2 := d &&& 7; let b2 := (d >>> 3) &&& 7; let c2 := (d >>> 6) &&& 7; let e2 := d >>> 9
  let (x2, y2) := if e1 == 0 then (a2, b2) else (b2, a2)
  qm a1 x2 + 8 * qm b1 y2 + 64 * qm c1 c2 + 512 * (e1 ^^^ e2)
public meta def lt (x : Nat) : Nat := (x &&& 1) + 2 * (x >>> 2)
public meta def clsN (c : Nat) : Nat :=
  let x := c &&& 7; let y := (c >>> 3) &&& 7; let z := (c >>> 6) &&& 7
  if c >>> 9 == 0 then
    if lt x != 0 && lt y != 0 && lt z != 0 then (TT >>> (5 * (16 * lt x + 4 * lt y + lt z))) &&& 31
    else if (x == 2) == (y == 2) && (z == 2) != (x == 2) then 23 else 22
  else if lt z == 0 then 21 else 17 + lt z
public meta def repR (k : Nat) : Nat := (REPT >>> (10 * k)) &&& 1023
public meta def isInvR (c : Nat) : Bool := nz (mulR c c) == 0 && nz c != 0
public meta def rowsN : List Nat :=
  [4352, 7328, 16928, 21088, 6834, 3762, 1682, 2674, 4754, 7826, 8818, 5746, 11590, 13763, 9544,
   13701, 15874, 11664, 14640, 13617, 10641, 14671, 11695, 12740, 11559, 15905, 8196, 6181, 6212,
   2151, 136, 167, 2244, 229, 260, 12625, 12656, 14724, 12709, 2544, 529, 560]

public meta def cls (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let mut W : Array Nat := #[]
  for c in (List.range 1024).reverse do
    if isInvR c then
      let r := repR (clsN c)
      match (List.range 1024).find? (fun g => nz (mulR g c) == nz (mulR r g)) with
      | some g => W := W.push (c + 1024 * g)
      | none => throw s!"no conjugator for {c}"
  return #[(`W, nats W.toList)]

public meta def rows (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let mut W : Array Nat := #[]
  for r in rowsN do
    let e := repR (r &&& 31)
    let ok := fun w => nz (mulR w e) == nz (mulR e w) && isInvR w && nz w != nz e &&
      isInvR (mulR w e) && clsN w == (r >>> 5) &&& 31 && clsN (mulR w e) == r >>> 10
    match (List.range 1024).find? ok with
    | some w => W := W.push (w + 1024 * r)
    | none => throw s!"no witness for row {r}"
  return #[(`W, nats W.toList)]

public meta def pairs (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let all := reps fun _ => true
  let A := reps fun a => mulM a a != 0 && mulM a a != 18
  let gi := all.map fun g => (g, (all.find? fun h => mulM g h == 0).getD 0)
  let least := fun a => (gi.map fun (g, h) => mulM (mulM g a) h).foldl min 1024
  let P := (A.map least).eraseDups
  let mut X : Array Nat := #[]
  for a in A do
    let r := least a
    match all.find? (fun g => mulM g a == mulM r g) with
    | some g => X := X.push (a + 1024 * g + 1048576 * r)
    | none => throw s!"no conjugator for {a}"
  return #[(`A, nats A), (`P, nats P), (`X, nats X.toList)]

end Certificates.FzFus.Twin
