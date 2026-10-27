module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section KitB

variable {W : Type} [CommGroup W]

@[expose] def OmegaCentTriv (H : Subgroup (MulAut W)) : Prop :=
  ∀ φ : MulAut W, (∀ h ∈ H, φ * h = h * φ) → φ = 1

@[expose] def OmegaSingTrans (H : Subgroup (MulAut W)) : Prop :=
  ∀ w w' : W, w ≠ 1 → w' ≠ 1 → Nat.card (ptCent H w) = 960 → Nat.card (ptCent H w') = 960 →
    ∃ h ∈ H, h w = w'

@[expose] def OmegaA2Fix (H : Subgroup (MulAut W)) : Prop :=
  ∀ S : Subgroup (MulAut W), IsSylowIn 2 S H → ∀ A ∈ E3.aSet 2 H, A ≤ S →
    ∀ w : W, w ≠ 1 → Nat.card (ptCent H w) = 960 → (ptCent S w).relIndex S ≤ 4 →
      ∀ a ∈ A, a w = w

@[expose] def OmegaA2Join (H : Subgroup (MulAut W)) : Prop :=
  ∀ S : Subgroup (MulAut W), IsSylowIn 2 S H → ∀ 𝒮 : Set (Subgroup (MulAut W)),
    (∀ A ∈ 𝒮, A ∈ E3.aSet 2 H ∧ A ≤ S) →
    (∀ A ∈ 𝒮, ∀ n ∈ normalizer (S : Set (MulAut W)) ⊓ H,
      A.map (MulAut.conj n).toMonoidHom ∈ 𝒮) →
    ∃ E : Subgroup (MulAut W),
      E ≤ normalizer ((⨆ A ∈ 𝒮, A : Subgroup (MulAut W)) : Set (MulAut W)) ⊓ H ∧
        IsPGroup 3 E ∧ ¬ IsCyclic E

end KitB

@[expose] def OmegaKitB : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1 →
      OmegaCentTriv H ∧ OmegaSingTrans H ∧ OmegaA2Fix H ∧ OmegaA2Join H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
