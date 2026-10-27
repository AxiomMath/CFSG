module

public import CFSG.Quasithin.H13.L32NMat8Inputs
public import CFSG.Quasithin.Background.G2UClosure
public import Mathlib

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U

@[expose] def mulS (A B : List ℕ) : List ℕ :=
  [mv8 A (B.getD 0 0), mv8 A (B.getD 1 0), mv8 A (B.getD 2 0), mv8 A (B.getD 3 0),
    mv8 A (B.getD 4 0), mv8 A (B.getD 5 0), mv8 A (B.getD 6 0), mv8 A (B.getD 7 0)]

@[expose] def commS (A B : List ℕ) : Bool := mulS A B == mulS B A

@[expose] def trS (A : List ℕ) : List ℕ :=
  (List.range 8).map fun j =>
    (List.range 8).foldl (fun acc i => if (A.getD i 0).testBit j then acc + 2 ^ i else acc) 0

@[expose] def jS : List ℕ := [16, 32, 64, 128, 1, 2, 4, 8]

@[expose] def invS (A : List ℕ) : List ℕ := mulS (mulS jS (trS A)) jS

@[expose] def conjS (g x : List ℕ) : List ℕ := mulS (mulS g x) (invS g)

@[expose] def conjStepS (x gg : List ℕ) : List ℕ := mulS (mulS (gg.take 8) x) (gg.drop 8)

@[expose] def validS (A : List ℕ) : Bool := A.length == 8 && A.all fun c => decide (c < 256)

@[expose] def spS (A : List ℕ) : Bool :=
  validS A && (List.range 8).all fun i => (List.range 8).all fun j =>
    b4N (A.getD i 0) (A.getD j 0) == (i + 4 == j || j + 4 == i)

@[expose] def fixS (A : List ℕ) : ℕ := ((List.range 256).filter fun v => mv8 A v == v).length

@[expose] def aTypeS (A : List ℕ) : Bool := (List.range 256).all fun v => !(b4N v (mv8 A v))

@[expose] def tabS (gens : List (List ℕ)) (n : ℕ) : Array (List ℕ) :=
  build one8 mulS gens (bfsParents one8 mulS gens n)

@[expose] def tabOK (gens : List (List ℕ)) (es : Array (List ℕ)) (n : ℕ) : Bool :=
  es.size == n && closedCheck mulS gens es && distinctCheck es && allCheck validS es &&
    gens.all spS

@[expose] def orbS (r : List ℕ) (gp : List (List ℕ)) (n : ℕ) : Array (List ℕ) :=
  build r conjStepS gp (bfsParents r conjStepS gp n)

@[expose] def cmapS (es inv : Array (List ℕ)) (a : List ℕ) : Std.HashMap (List ℕ) ℕ :=
  (List.range es.size).foldl (fun m t => m.insert (mulS (mulS (es.getD t []) a) (inv.getD t [])) t)
    {}

@[expose] def cfoundS (es : Array (List ℕ)) (m : Std.HashMap (List ℕ) ℕ) (a x : List ℕ) : Bool :=
  match m.get? x with
  | some t => decide (t < es.size) && mulS (es.getD t []) a == mulS x (es.getD t [])
  | none => false

@[expose] def z0S : List ℕ := [16, 2, 4, 8, 17, 32, 64, 128]

@[expose] def z1S : List ℕ := [1, 32, 4, 8, 16, 34, 64, 128]

@[expose] def z2S : List ℕ := [1, 2, 64, 8, 16, 32, 68, 128]

@[expose] def z3S : List ℕ := [1, 2, 4, 128, 16, 32, 64, 136]

@[expose] def tS : List ℕ := [2, 4, 1, 8, 32, 64, 16, 128]

@[expose] def zzS : List ℕ := mulS z0S z1S

@[expose] def z012S : List ℕ := mulS zzS z2S

@[expose] def z0123S : List ℕ := mulS z012S z3S

@[expose] def e0Gens : List (List ℕ) := [z0S, z1S, z2S, z3S]

@[expose] def pGens : List (List ℕ) := [z0S, z1S, z2S, z3S, tS]

@[expose] def l1S : List (List ℕ) :=
  [z0S, mulS z0S z0S, z1S, mulS z1S z1S, z2S, mulS z2S z2S, z3S, mulS z3S z3S]

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
