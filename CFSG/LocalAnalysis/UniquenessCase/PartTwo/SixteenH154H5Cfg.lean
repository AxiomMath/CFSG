module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

structure s16h_H5Cfg (A L : Subgroup (MulAut W)) (t : MulAut W) : Prop where
  elem : ∀ w : W, w ^ 2 = 1
  mem : t ∈ A
  sq : t ^ 2 = 1
  ne : t ≠ 1
  tr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3
  conc : Conc4_136W A t L
  comp : IsComponentOf L A
  thin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1

@[expose] def s16h_H5Block (A L : Subgroup (MulAut W)) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
    E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
    Nat.card E ≤ q ^ 2 * Nat.card ↥(E ⊓ centSub (commSub ⊤ L))

@[expose] def s16h_H5RowL3 (L : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  ∃ k : ℕ, k ≤ 3 ∧ IsSLn ↥L 3 1 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L U Z k

@[expose] def s16h_H5RowA5 (L : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  ∃ k : ℕ, k ≤ 3 ∧
    ((IsOmegaMinus ↥L 4 1 ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 1) L U Z k) ∨
      (UC22.IsAlt ↥L 5 ∧ SumOfNat (fun H U Z => AlternatingNatural H U Z 5) L U Z k))

@[expose] def s16h_H5RowSL2 (L : Subgroup (MulAut W)) (U Z : Subgroup W) (a : ℕ) : Prop :=
  IsSLn ↥L 2 a ∧ BinaryNaturalSL L U Z 2 a

@[expose] def s16h_H5RowO4 (L : Subgroup (MulAut W)) (U Z : Subgroup W) (m : ℕ) : Prop :=
  IsOmegaMinus ↥L 4 m ∧ NatOmegaMinus L U Z 4 m

@[expose] def s16h_H5RowSt8 (L : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  IsL3 ↥L 1 ∧ E3.mQuot U Z = 8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
