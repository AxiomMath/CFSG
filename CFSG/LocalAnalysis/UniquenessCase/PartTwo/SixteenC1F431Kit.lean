module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section KitC

variable {W : Type} [CommGroup W]

@[expose] def OmegaFormSing (H : Subgroup (MulAut W)) : Prop :=
  ∀ Q : W → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q H → ∀ w : W, w ≠ 1 →
    (Q w = 0 ↔ Nat.card (ptCent H w) = 960)

@[expose] def OmegaNormIsom (H : Subgroup (MulAut W)) : Prop :=
  ∀ Q : W → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q H →
    ∀ x ∈ normalizer (H : Set (MulAut W)), ∀ w : W, Q (x w) = Q w

@[expose] def OmegaOuterNons (H : Subgroup (MulAut W)) : Prop :=
  ∀ Q : W → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q H →
    ∀ x ∈ normalizer (H : Set (MulAut W)), x ∉ H → ∃ w : W, Q (x w * w⁻¹) ≠ 0

@[expose] def OmegaRankLe4 (H : Subgroup (MulAut W)) : Prop :=
  ∀ E : Subgroup (MulAut W), E ≤ normalizer (H : Set (MulAut W)) → IsElemAbelian2 E →
    Nat.card E ≤ 16

@[expose] def OmegaTransPair (H : Subgroup (MulAut W)) : Prop :=
  ∀ E : Subgroup (MulAut W), E ≤ normalizer (H : Set (MulAut W)) → IsElemAbelian2 E →
    Nat.card E = 16 → ¬ E ≤ H →
      ∃ a₁ ∈ E, ∃ a₂ ∈ E, Nat.card (commV (Subgroup.zpowers a₁)) = 2 ∧
        Nat.card (commV (Subgroup.zpowers a₂)) = 2 ∧
          fixV (Subgroup.zpowers a₁) ⊔ fixV (Subgroup.zpowers a₂) = ⊤

end KitC

@[expose] def OmegaKitC : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1 →
      OmegaFormSing H ∧ OmegaNormIsom H ∧ OmegaOuterNons H ∧ OmegaRankLe4 H ∧ OmegaTransPair H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
