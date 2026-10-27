module

public import Certificates.Data.OmegaS107Facts

public section

namespace Certificates.OmegaCY

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def LemmaY (B0 B2 : Subgroup P45) : Prop :=
  ∀ (H : Type) [Group H] (Φ : H →* P45 × ℤˣ), Function.Injective Φ → ∀ α : H →* H,
    (∀ y, α (α y) = y) → ∀ t z : H, Φ t = (1, -1) → Φ z = (Certificates.OmegaT0.z0 (), 1) →
      α t = t * z → α z = z → (∀ g, g ∈ B0.prod ⊤ ∨ g ∈ B2.prod ⊤ → ∃ y, Φ y = g) →
        (∀ y, Φ y ∈ B0.prod ⊤ → Φ (α y) ∈ B2.prod ⊤) →
          (∀ y, Φ y ∈ B2.prod ⊤ → Φ (α y) ∈ B0.prod ⊤) →
            ∃ y : H, y⁻¹ * α y * (y⁻¹ * α y) = 1 ∧ y⁻¹ * α y ≠ 1 ∧ y⁻¹ * α y ≠ z

@[expose] def Facts : Prop :=
  ∀ (T B0 B2 : Subgroup P45) (y2 : P45), QT0.originalSubgroup ≤ T →
    T ≤ QA45.originalSubgroup → IsPGroup 2 T → (∃ w ∈ T, w ∉ QT0.originalSubgroup) →
      Certificates.OmegaS107.M107 T B2 y2 → B0 ≤ QT0.originalSubgroup →
        (∀ a ∈ B0, ∀ b ∈ B0, a * b = b * a) → Nat.card B0 = 16 → LemmaY B0 B2

end Certificates.OmegaCY

end
