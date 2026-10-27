module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin

namespace SBc16

@[expose] def NoFiveD8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], Nat.card V = 25 → (∀ x : V, x ^ 5 = 1) →
    ∀ V₁ V₂ : Subgroup V, Nat.card V₁ = 5 → Nat.card V₂ = 5 → V₁ ⊓ V₂ = ⊥ →
      ∀ (A : Subgroup (MulAut V)) (σ τ : MulAut V), σ ∈ A → τ ∈ A →
        (∀ x ∈ V₂, σ x = x) → (∀ x ∈ V₁, σ x = x⁻¹) →
        V₁.map τ.toMonoidHom = V₂ → V₂.map τ.toMonoidHom = V₁ →
        ¬ 16 ∣ Nat.card A → ∀ α ∈ A, orderOf α ≠ 5

end SBc16

end CFSG.Quasithin
