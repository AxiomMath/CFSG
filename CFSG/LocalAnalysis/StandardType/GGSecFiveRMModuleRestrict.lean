module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

section Module

theorem ggLin_restrict_exists
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (U : Submodule (ZMod p) V)
    (hU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) :
    ∃ r : ↥A →* (↥U ≃ₗ[ZMod p] ↥U), ∀ (a : ↥A) (u : ↥U), ((r a u : ↥U) : V) = (a : V ≃ₗ[ZMod p] V) u := by
  have hmap : ∀ a : ↥A, U.map (a : V →ₗ[ZMod p] V) = U := by
    intro a
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hU (a : V ≃ₗ[ZMod p] V) a.2 y hy
    · intro hx
      exact ⟨(a : V ≃ₗ[ZMod p] V).symm x,
        hU ((a : V ≃ₗ[ZMod p] V)⁻¹) (A.inv_mem a.2) x hx,
        (a : V ≃ₗ[ZMod p] V).apply_symm_apply x⟩
  let f : ↥A → (↥U ≃ₗ[ZMod p] ↥U) :=
    fun a => LinearEquiv.ofSubmodules (a : V ≃ₗ[ZMod p] V) U U (hmap a)
  refine ⟨MonoidHom.mk' f ?_, ?_⟩
  · intro a b
    ext u
    simp only [f, LinearEquiv.ofSubmodules_apply, LinearEquiv.mul_apply, Subgroup.coe_mul]
  · intro a u
    change ((f a u : ↥U) : V) = (a : V ≃ₗ[ZMod p] V) u
    exact LinearEquiv.ofSubmodules_apply (a : V ≃ₗ[ZMod p] V) (hmap a) u

end Module

end CFSG.StandardType

end
