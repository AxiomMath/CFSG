module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinDef
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin

@[expose] def A6Amt : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Γ L : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V) (s : MulAut V),
      L ≤ Γ → (∀ γ ∈ Γ, ∀ l ∈ L, γ * l * γ⁻¹ ∈ L) → s ∈ Γ → W₁ ⊔ W₂ = ⊤ →
      (∀ l ∈ L, ∀ w ∈ W₁, l w ∈ W₁) → (∀ l ∈ L, ∀ w ∈ W₂, l w ∈ W₂) →
      (∀ w : V, w ∈ W₂ ↔ s⁻¹ w ∈ W₁) →
      rk W₁ = 4 → (∀ S : Subgroup V, S ≤ W₁ → (∀ l ∈ L, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = W₁) →
      Nonempty (L ≃* alternatingGroup (Fin 6)) →
      (∃ x ∈ L, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l ∈ L, l * x * l⁻¹ ≠ s * x * s⁻¹) →
      ∀ A : Subgroup (MulAut V), IsA2 Γ A → commSeries A 2 = ⊥ → rkIdx (fixV A) ≤ 2 * rk A →
        rkIdx (fixV A) = 2 * rk A ∧ ∃ a ∈ A, rk A + 2 ≤ A6Rank a

end CFSG.Quasithin
