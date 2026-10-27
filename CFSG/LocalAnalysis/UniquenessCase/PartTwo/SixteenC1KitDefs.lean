module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Kit

variable {W : Type} [CommGroup W]

@[expose] def OmegaGeo2 (H : Subgroup (MulAut W)) : Prop :=
  ∀ P : Subgroup W, Nat.card P = 4 → ∃ φ ∈ H, orderOf φ = 3 ∧ ∀ p ∈ P, φ p = p

@[expose] def OmegaIrr (H : Subgroup (MulAut W)) : Prop :=
  ∀ z : W, z ≠ 1 → Nat.card (ptCent H z) = 960 → ∀ S : Subgroup W,
    StableUnder (ptCent H z) S →
      Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 32 ∨ Nat.card S = 64

@[expose] def OmegaNoTrans (H : Subgroup (MulAut W)) : Prop :=
  ∀ t ∈ H, ∀ c : W, c ≠ 1 → (∀ w : W, t w = w ∨ t w = w * c) → t = 1

end Kit

@[expose] def OmegaKit : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1 → OmegaGeo2 H ∧ OmegaIrr H ∧ OmegaNoTrans H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
