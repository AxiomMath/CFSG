module

public import CFSG.Quasithin.Background.Harris.Ln2.Basic

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def normConj {L : Subgroup (GLV V)} (γ : GLV V) (hγ : ∀ l ∈ L, γ * l * γ⁻¹ ∈ L)
    (hγ' : ∀ l ∈ L, γ⁻¹ * l * γ ∈ L) : ↥L ≃* ↥L where
  toFun l := ⟨γ * l * γ⁻¹, hγ l l.2⟩
  invFun l := ⟨γ⁻¹ * l * γ, hγ' l l.2⟩
  left_inv l := Subtype.ext (by simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left])
  right_inv l := Subtype.ext (by simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left])

theorem exists_intertwiner {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    {L : Subgroup (GLV V)} {θ : ↥L ≃* G} {τ : Representation (ZMod 2) G W}
    {β : V ≃ₗ[ZMod 2] W} (h : ActsAs L θ τ β) (γ : GLV V) (hγ : ∀ l ∈ L, γ * l * γ⁻¹ ∈ L)
    (hγ' : ∀ l ∈ L, γ⁻¹ * l * γ ∈ L) :
    ∃ (M : W ≃ₗ[ZMod 2] W) (σ : G ≃* G), (∀ v, M (β v) = β (γ v)) ∧
      ∀ x w, M (τ x w) = τ (σ x) (M w) := by
  refine ⟨β.symm.trans (γ.trans β), (θ.symm.trans (normConj γ hγ hγ')).trans θ, fun v => ?_,
    fun x w => ?_⟩
  · simp
  · obtain ⟨v, rfl⟩ := β.surjective w
    have h1 : τ x (β v) = β (((θ.symm x : ↥L) : GLV V) v) := by
      rw [h, MulEquiv.apply_symm_apply]
    have h2 : ∀ u, (β.symm.trans (γ.trans β) : W ≃ₗ[ZMod 2] W) (β u) = β (γ u) := fun u => by simp
    rw [h1, h2, h2, MulEquiv.trans_apply, MulEquiv.trans_apply, ← h]
    simp [normConj]

end CFSG.Quasithin.G11.Harris.Ln2
