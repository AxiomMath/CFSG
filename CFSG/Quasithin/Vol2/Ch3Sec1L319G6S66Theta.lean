module

public import CFSG.Quasithin.Vol2.Ch3zSetup

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.Ch3z

theorem chiefAut_mulEquiv_of_centralizerMod_eq {G : Type} [Group G] {H L N L' N' : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hHL' : H ≤ Subgroup.normalizer (L' : Set G)) (hHN' : H ≤ Subgroup.normalizer (N' : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hNL' : N' ≤ Subgroup.normalizer (L' : Set G))
    (hJ : centralizerMod L H N = centralizerMod L' H N') :
    ∃ θ : ↥(chiefAut H L N) ≃* ↥(chiefAut H L' N'),
      ∀ g : ↥H, θ (chiefHom hHL hHN g) = chiefHom hHL' hHN' g := by
  have hker : (chiefHom hHL hHN).ker = (chiefHom hHL' hHN').ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, chiefHom_eq_one_iff hHL hHN hNL,
      chiefHom_eq_one_iff hHL' hHN' hNL', hJ]
  have hwd : ∀ g₁ g₂ : ↥H, chiefHom hHL hHN g₁ = chiefHom hHL hHN g₂ →
      chiefHom hHL' hHN' g₁ = chiefHom hHL' hHN' g₂ := by
    intro g₁ g₂ h
    have hmem : g₁ * g₂⁻¹ ∈ (chiefHom hHL hHN).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv] at hmem
    exact mul_inv_eq_one.mp hmem
  let θf : ↥(chiefAut H L N) → ↥(chiefAut H L' N') :=
    fun x => chiefHom hHL' hHN' (Function.surjInv (chiefHom_surjective hHL hHN) x)
  have hθf : ∀ g : ↥H, θf (chiefHom hHL hHN g) = chiefHom hHL' hHN' g := fun g =>
    hwd _ _ (Function.surjInv_eq (chiefHom_surjective hHL hHN) _)
  let θ : ↥(chiefAut H L N) →* ↥(chiefAut H L' N') := MonoidHom.mk' θf (by
    intro x y
    obtain ⟨g, rfl⟩ := chiefHom_surjective hHL hHN x
    obtain ⟨g', rfl⟩ := chiefHom_surjective hHL hHN y
    rw [← map_mul, hθf, hθf, hθf, map_mul])
  have hθ : ∀ g : ↥H, θ (chiefHom hHL hHN g) = chiefHom hHL' hHN' g := fun g => hθf g
  refine ⟨MulEquiv.ofBijective θ ⟨?_, ?_⟩, hθ⟩
  · intro x y hxy
    obtain ⟨g, rfl⟩ := chiefHom_surjective hHL hHN x
    obtain ⟨h, rfl⟩ := chiefHom_surjective hHL hHN y
    rw [hθ, hθ] at hxy
    have h1 : g * h⁻¹ ∈ (chiefHom hHL' hHN').ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  · intro y
    obtain ⟨g, hg⟩ := chiefHom_surjective hHL' hHN' y
    exact ⟨chiefHom hHL hHN g, by rw [hθ, hg]⟩

end CFSG.Quasithin.H13.L319.S66

end
