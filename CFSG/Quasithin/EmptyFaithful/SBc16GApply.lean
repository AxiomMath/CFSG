module

public import CFSG.Quasithin.EmptyFaithful.SBc16Defs

public section

namespace CFSG.Quasithin

namespace SBc16

theorem noFiveD8_apply (hF : NoFiveD8) {V : Type} [Group V] [Finite V]
    (hc : ∀ a b : V, a * b = b * a) (hcard : Nat.card V = 25)
    (V₁ V₂ : Subgroup V) (h1 : Nat.card V₁ = 5) (h2 : Nat.card V₂ = 5) (hd : V₁ ⊓ V₂ = ⊥)
    (hsup : V₁ ⊔ V₂ = ⊤) (A : Subgroup (MulAut V)) (σ τ : MulAut V) (hσ : σ ∈ A) (hτ : τ ∈ A)
    (hσ₂ : ∀ x ∈ V₂, σ x = x) (hσ₁ : ∀ x ∈ V₁, σ x = x⁻¹)
    (hτ₁ : V₁.map τ.toMonoidHom = V₂) (hτ₂ : V₂.map τ.toMonoidHom = V₁)
    (h16 : ¬ 16 ∣ Nat.card A) : ∀ α ∈ A, orderOf α ≠ 5 := by
  let : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hexp : ∀ x : V, x ^ 5 = 1 := by
    intro x
    have hx : x ∈ V₁ ⊔ V₂ := by rw [hsup]; exact Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    have hy5 : y ^ 5 = 1 := by
      have := pow_card_eq_one' (G := V₁) (x := ⟨y, hy⟩)
      rw [h1] at this
      exact congrArg Subtype.val this
    have hz5 : z ^ 5 = 1 := by
      have := pow_card_eq_one' (G := V₂) (x := ⟨z, hz⟩)
      rw [h2] at this
      exact congrArg Subtype.val this
    rw [mul_pow, hy5, hz5, one_mul]
  exact hF V hcard hexp V₁ V₂ h1 h2 hd A σ τ hσ hτ hσ₂ hσ₁ hτ₁ hτ₂ h16

end SBc16

end CFSG.Quasithin
