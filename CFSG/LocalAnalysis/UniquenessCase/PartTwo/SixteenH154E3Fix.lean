module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

@[expose] def s16h_H5A5Sum (L : Subgroup (MulAut W)) (U Z : Subgroup W) (k : ℕ) : Prop :=
  (IsOmegaMinus ↥L 4 1 ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 1) L U Z k) ∨
    (UC22.IsAlt ↥L 5 ∧ SumOfNat (fun H U Z => AlternatingNatural H U Z 5) L U Z k)

@[expose] def s16h_H5L3Sum (L : Subgroup (MulAut W)) (U Z : Subgroup W) (k : ℕ) : Prop :=
  IsSLn ↥L 3 1 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L U Z k

theorem s16h_H5RowA5_iff (L : Subgroup (MulAut W)) (U Z : Subgroup W) :
    s16h_H5RowA5 L U Z ↔ ∃ k : ℕ, k ≤ 3 ∧ s16h_H5A5Sum L U Z k :=
  Iff.rfl

theorem s16h_H5RowL3_iff (L : Subgroup (MulAut W)) (U Z : Subgroup W) :
    s16h_H5RowL3 L U Z ↔ ∃ k : ℕ, k ≤ 3 ∧ s16h_H5L3Sum L U Z k :=
  Iff.rfl

@[expose] def s16h_H5Fix [Finite W] (A L : Subgroup (MulAut W)) (q : ℕ) : Prop :=
  ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
    q ^ 2 * Nat.card ↥(E ⊓ centSub (commSub ⊤ L)) ≤ Nat.card ↥E →
    ∀ w ∈ commSub (⊤ : Subgroup W) L, w ≠ 1 →
      ∃ g ∈ L, ∃ b ∈ E, b ∉ centSub (commSub ⊤ L) ∧ (g * b * g⁻¹) w = w

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
