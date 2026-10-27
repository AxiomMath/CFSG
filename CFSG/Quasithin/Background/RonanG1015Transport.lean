module

public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.Quasithin

namespace RonanG1015

@[expose] def IndAll {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  ∀ α : ↥K ≃* ↥K, ∃ g : G, ∀ k : ↥K, ((α k : ↥K) : G) = g * (k : G) * g⁻¹

section Transport

variable {G G' : Type*} [Group G] [Group G'] (Φ : G ≃* G') {K : Subgroup G} {K' : Subgroup G'}

@[expose] noncomputable def subEquiv (hK : K.map Φ.toMonoidHom = K') : ↥K ≃* ↥K' :=
  (Subgroup.equivMapOfInjective K Φ.toMonoidHom Φ.injective).trans (MulEquiv.subgroupCongr hK)

theorem coe_subEquiv (hK : K.map Φ.toMonoidHom = K') (k : ↥K) :
    ((subEquiv Φ hK k : ↥K') : G') = Φ (k : G) := rfl

@[expose] noncomputable def transportAut (hK : K.map Φ.toMonoidHom = K') (α : ↥K ≃* ↥K) : ↥K' ≃* ↥K' :=
  (subEquiv Φ hK).symm.trans (α.trans (subEquiv Φ hK))

theorem transportAut_apply (hK : K.map Φ.toMonoidHom = K') (α : ↥K ≃* ↥K) (k : ↥K) :
    transportAut Φ hK α (subEquiv Φ hK k) = subEquiv Φ hK (α k) := by
  simp [transportAut]

theorem induced_of_transport (hK : K.map Φ.toMonoidHom = K') (α : ↥K ≃* ↥K) (g' : G')
    (h : ∀ x : ↥K', ((transportAut Φ hK α x : ↥K') : G') = g' * (x : G') * g'⁻¹) :
    ∃ g : G, ∀ k : ↥K, ((α k : ↥K) : G) = g * (k : G) * g⁻¹ := by
  refine ⟨Φ.symm g', fun k => ?_⟩
  have h1 := h (subEquiv Φ hK k)
  rw [transportAut_apply, coe_subEquiv, coe_subEquiv] at h1
  apply Φ.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem IndAll.of_equiv (hK : K.map Φ.toMonoidHom = K') (h : IndAll K') : IndAll K := by
  intro α
  obtain ⟨g', hg'⟩ := h (transportAut Φ hK α)
  exact induced_of_transport Φ hK α g' hg'

end Transport

end RonanG1015

end CFSG.Quasithin
