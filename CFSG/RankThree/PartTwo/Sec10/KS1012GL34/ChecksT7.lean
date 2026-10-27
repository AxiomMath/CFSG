module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Defs
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks
public meta import CFSG.Fischer.F4
public meta import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Defs
public meta import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34

open CFSG.Fischer
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

@[expose] def t7Pt : Fin 6 → Fin 6 → Fin 3 → F4 := ![
  ![![1, 1, 1], ![1, om2, om2], ![1, F4.ω, om2], ![1, 1, F4.ω], ![1, om2, F4.ω], ![1, F4.ω, 1]],
  ![![0, 0, 1], ![1, F4.ω, F4.ω], ![0, 1, 0], ![1, 0, 0], ![1, 1, om2], ![1, om2, 1]],
  ![![0, 0, 1], ![1, om2, om2], ![1, 0, 0], ![1, F4.ω, 1], ![1, 1, F4.ω], ![0, 1, 0]],
  ![![1, 1, 1], ![1, om2, 1], ![1, 1, om2], ![1, F4.ω, om2], ![1, om2, F4.ω], ![1, F4.ω, F4.ω]],
  ![![1, 1, F4.ω], ![1, om2, om2], ![1, F4.ω, 1], ![1, 1, om2], ![1, F4.ω, F4.ω], ![1, om2, 1]],
  ![![0, 0, 1], ![1, F4.ω, om2], ![1, om2, F4.ω], ![1, 1, 1], ![1, 0, 0], ![0, 1, 0]]]

@[expose] def cols (f : Fin 3 → Fin 3 → F4) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun r k => f k r

@[expose] def t7Base (i : Fin 6) (k : Fin 3) : Fin 3 → F4 :=
  t7Pt i (Fin.castLE (by decide) k)

@[expose] def t7V (i : Fin 6) : Matrix (Fin 3) (Fin 3) F4 := cols (t7Base i)

@[expose] def t7Vinv : Fin 6 → Matrix (Fin 3) (Fin 3) F4 := ![
  !![F4.ω, 0, om2; om2, 1, F4.ω; 0, 1, 1],
  !![F4.ω, 0, 1; 1, 0, 0; F4.ω, 1, 0],
  !![0, 1, 1; 0, F4.ω, 0; 1, F4.ω, 0],
  !![1, om2, om2; om2, om2, 0; om2, 0, om2],
  !![1, 1, om2; 1, F4.ω, F4.ω; 1, om2, 1],
  !![1, 1, 1; om2, 1, 0; F4.ω, 1, 0]]

@[expose] def t7Det (M : Matrix (Fin 3) (Fin 3) F4) : F4 :=
  M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1) - M 0 1 * (M 1 0 * M 2 2 - M 1 2 * M 2 0)
    + M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0)

@[expose] def t7Mm (A B : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4 :=
  !![A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 0 2 * B 2 0, A 0 0 * B 0 1 + A 0 1 * B 1 1 + A 0 2 * B 2 1,
      A 0 0 * B 0 2 + A 0 1 * B 1 2 + A 0 2 * B 2 2;
    A 1 0 * B 0 0 + A 1 1 * B 1 0 + A 1 2 * B 2 0, A 1 0 * B 0 1 + A 1 1 * B 1 1 + A 1 2 * B 2 1,
      A 1 0 * B 0 2 + A 1 1 * B 1 2 + A 1 2 * B 2 2;
    A 2 0 * B 0 0 + A 2 1 * B 1 0 + A 2 2 * B 2 0, A 2 0 * B 0 1 + A 2 1 * B 1 1 + A 2 2 * B 2 1,
      A 2 0 * B 0 2 + A 2 1 * B 1 2 + A 2 2 * B 2 2]

@[expose] def t7Mv (M : Matrix (Fin 3) (Fin 3) F4) (v : Fin 3 → F4) : Fin 3 → F4 :=
  ![M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2, M 1 0 * v 0 + M 1 1 * v 1 + M 1 2 * v 2,
    M 2 0 * v 0 + M 2 1 * v 1 + M 2 2 * v 2]

@[expose] def t7M (i : Fin 6) (q : (Fin 3 → Fin 6) × (Fin 3 → F4)) :
    Matrix (Fin 3) (Fin 3) F4 :=
  t7Mm (cols fun k => q.2 k • t7Pt i (q.1 k)) (t7Vinv i)

@[expose] def t7Scal : List F4 := [1, F4.ω, om2]

@[expose] def t7Stab (i : Fin 6) (M : Matrix (Fin 3) (Fin 3) F4) : Prop :=
  ∀ k : Fin 6, ∃ j : Fin 6, ∃ c ∈ t7Scal, t7Mv M (t7Pt i k) = fun r => c * t7Pt i j r

instance (i : Fin 6) (M : Matrix (Fin 3) (Fin 3) F4) : Decidable (t7Stab i M) := by
  unfold t7Stab
  infer_instance

@[expose, irreducible] def t7Tup (i : Fin 6) : Finset ((Fin 3 → Fin 6) × (Fin 3 → F4)) :=
  Finset.univ.filter fun q => t7Det (t7M i q) = 1 ∧ t7Stab i (t7M i q)

@[expose] def t7Idx (i : Fin 6) (M : Matrix (Fin 3) (Fin 3) F4) (k : Fin 6) : Fin 6 :=
  ((List.finRange 6).find? fun j =>
    decide (∃ c : F4, c ≠ 0 ∧ Matrix.mulVec M (t7Pt i k) = c • t7Pt i j)).getD 0

@[expose] def t7Adj (A : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4 :=
  !![A 1 1 * A 2 2 - A 1 2 * A 2 1, -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
    -(A 1 0 * A 2 2) + A 1 2 * A 2 0, A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
    A 1 0 * A 2 1 - A 1 1 * A 2 0, -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0]

@[expose] def t7PermOf (f g : Fin 6 → Fin 6) : Equiv.Perm (Fin 6) :=
  if h : (∀ k, g (f k) = k) ∧ (∀ k, f (g k) = k) then ⟨f, g, h.1, h.2⟩ else 1

@[expose] def t7Perm (i : Fin 6) (M : Matrix (Fin 3) (Fin 3) F4) : Equiv.Perm (Fin 6) :=
  t7PermOf (t7Idx i M) (t7Idx i (t7Adj M))

@[expose] def t7Ker (i : Fin 6) : Finset ((Fin 3 → Fin 6) × (Fin 3 → F4)) :=
  (t7Tup i).filter fun q => t7Perm i (t7M i q) = 1

@[expose] def ptL (i k : Fin 6) : V3 := ⟨t7Pt i k 0, t7Pt i k 1, t7Pt i k 2⟩

@[expose] def isMultL (w u : V3) : Bool := NZL.any fun c => decide (w = smulV c u)

@[expose] def idxL (i : Fin 6) (A : M3) (k : Fin 6) : Fin 6 :=
  let w := mulV A (ptL i k)
  ((List.finRange 6).find? fun j => isMultL w (ptL i j)).getD 0

@[expose] def adjL (A : M3) : M3 :=
  ⟨A.a11 * A.a22 - A.a12 * A.a21, -(A.a01 * A.a22) + A.a02 * A.a21,
    A.a01 * A.a12 - A.a02 * A.a11, -(A.a10 * A.a22) + A.a12 * A.a20,
    A.a00 * A.a22 - A.a02 * A.a20, -(A.a00 * A.a12) + A.a02 * A.a10,
    A.a10 * A.a21 - A.a11 * A.a20, -(A.a00 * A.a21) + A.a01 * A.a20,
    A.a00 * A.a11 - A.a01 * A.a10⟩

@[expose] def permLOf (i : Fin 6) (A : M3) : Equiv.Perm (Fin 6) :=
  t7PermOf (idxL i A) (idxL i (adjL A))

@[expose] def scalMatL (c : F4) : M3 := ⟨c, 0, 0, 0, c, 0, 0, 0, c⟩

@[expose] def scalL (A : M3) : Bool := NZL.any fun c => decide (A = scalMatL c)

@[expose] def slL (_ : Unit := ()) : List M3 :=
  (allM3L ()).filter fun A => decide (detL A = 1)

@[expose] def piLS (S : List M3) (i : Fin 6) : List M3 :=
  S.filter fun A => stabLn i.val A

@[expose] def piL (i : Fin 6) : List M3 := piLS (slL ()) i

@[expose] def t7CheckAtS (S : List M3) (i : Fin 6) : Bool :=
  let PL := piLS S i
  let KL := PL.filter fun A => decide (permLOf i A = 1)
  decide PL.Nodup && decide (PL.length = 1080) &&
    PL.all (fun A => decide (Equiv.Perm.sign (permLOf i A) = 1)) &&
    decide (KL.length = 3) && KL.all scalL

@[expose] def t7CheckAt (i : Fin 6) : Bool := t7CheckAtS (slL ()) i

@[expose] def t7CheckAll (S : List M3) : Bool := decide (∀ i : Fin 6, t7CheckAtS S i = true)

@[expose] def t7Check (_ : Unit := ()) : Bool := t7CheckAll (slL ())


end CFSG.RankThree.PartTwo.Sec10.KS1012GL34

end
