module

public import Certificates.Data.CFSGNative.F4.Unitary
public import Certificates.Data.SmithEWData

public section

namespace CFSG.SmithE

open CFSG.F4.Native

@[expose] def f4sq (x : Nat) : Nat := f4mul x x

@[expose] def tri : Array (Nat × Nat × Nat) := #[(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5),
  (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5), (0, 4, 5), (1, 2, 3), (1, 2, 4),
  (1, 2, 5), (1, 3, 4), (1, 3, 5), (1, 4, 5), (2, 3, 4), (2, 3, 5), (2, 4, 5), (3, 4, 5)]

@[expose] def det3 (a b c d e f g h i : Nat) : Nat :=
  f4mul a (f4mul e i ^^^ f4mul f h) ^^^ f4mul b (f4mul d i ^^^ f4mul f g) ^^^
    f4mul c (f4mul d h ^^^ f4mul e g)

@[expose] def minor (g : Nat → Nat → Nat) (s t : Nat) : Nat :=
  let (r0, r1, r2) := tri[s]!
  let (c0, c1, c2) := tri[t]!
  det3 (g r0 c0) (g r0 c1) (g r0 c2) (g r1 c0) (g r1 c1) (g r1 c2) (g r2 c0) (g r2 c1) (g r2 c2)

@[expose] def compound (g : Nat → Nat → Nat) : Array Nat :=
  Array.ofFn (n := 200) fun st => minor g (st.val / 20) (st.val % 20)

@[expose] def wcoef (c t : Nat) : Nat := if t < 10 then coord c t else f4sq (coord c (19 - t))

@[expose] def wedgeAct (C : Array Nat) (c : Nat) : Nat :=
  (List.range 10).foldl (fun acc k =>
    acc + ((List.range 20).foldl (fun a t => a ^^^ f4mul C[k * 20 + t]! (wcoef c t)) 0) * 4 ^ k) 0

@[expose] def tvEntry (p i j : Nat) : Nat :=
  (if i = j then 1 else 0) ^^^ f4mul (coord p i) (f4sq (coord p j))

@[expose] def tvCols (k : Nat) : Array Nat :=
  let C := compound (tvEntry uPts[k]!)
  Array.ofFn (n := 20) fun m => wedgeAct C (2 ^ m.val)

@[expose] def applyCols (cols : Array Nat) (c : Nat) : Nat :=
  (List.range cols.size).foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) 0

@[expose] def pluck (W : Nat × Nat × Nat) (t : Nat) : Nat :=
  let (r0, r1, r2) := tri[t]!
  det3 (coord W.1 r0) (coord W.2.1 r0) (coord W.2.2 r0) (coord W.1 r1) (coord W.2.1 r1)
    (coord W.2.2 r1) (coord W.1 r2) (coord W.2.1 r2) (coord W.2.2 r2)

@[expose] def wedgeScalar (W : Nat × Nat × Nat) : Nat :=
  let t := ((List.range 20).find? fun t => pluck W t != 0).getD 0
  f4mul (pluck W (19 - t)) (pluck W t)

@[expose] def wedgeCode (W : Nat × Nat × Nat) : Nat :=
  (List.range 10).foldl (fun acc k => acc + f4mul (wedgeScalar W) (pluck W k) * 4 ^ k) 0

@[expose] def vecMask (W : Nat × Nat × Nat) : Nat :=
  (List.range 64).foldl (fun acc d =>
    acc ||| 2 ^ (scaleC (d % 4) W.1 ^^^ scaleC (d / 4 % 4) W.2.1 ^^^ scaleC (d / 16) W.2.2)) 0

@[expose] def atLeast : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, n => n != 0 && atLeast k (n &&& (n - 1))

@[expose] def wB (i : Nat) : Nat × Nat × Nat :=
  let x := wData[i]!
  (x % 4096, x / 4096 % 4096, x / 4096 / 4096)

@[expose] def wt (i : Nat) : Nat := wedgeCode (wB i)

@[expose] def wMask (i : Nat) : Nat := vecMask (wB i)

@[expose] def adjW (i j : Nat) : Bool := atLeast 16 (wMask i &&& wMask j)

end CFSG.SmithE
