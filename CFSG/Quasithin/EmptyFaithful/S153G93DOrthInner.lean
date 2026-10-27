module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace Orth

open CFSG.QuasithinUnique

variable {M G : Type*} [Group M] [Group G]

@[expose] def conjAut (K : Subgroup M) (a : M) (ha2 : a * a = 1)
    (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) : MulAut ↥K where
  toFun k := ⟨a * k * a⁻¹, haN k k.2⟩
  invFun k := ⟨a * k * a⁻¹, haN k k.2⟩
  left_inv k := Subtype.ext (by
    have e : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    calc a * (a * (k : M) * a⁻¹) * a⁻¹ = (a * a) * k * (a⁻¹ * a⁻¹) := by group
      _ = k := by rw [ha2, e, ha2]; group)
  right_inv k := Subtype.ext (by
    have e : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    calc a * (a * (k : M) * a⁻¹) * a⁻¹ = (a * a) * k * (a⁻¹ * a⁻¹) := by group
      _ = k := by rw [ha2, e, ha2]; group)
  map_mul' x y := Subtype.ext (by
    show a * ((x : M) * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹)
    group)

@[expose] def transConj {K : Subgroup M} (θ : G ≃* ↥K) (a : M) (ha2 : a * a = 1)
    (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) : MulAut G :=
  θ.trans ((conjAut K a ha2 haN).trans θ.symm)

theorem coe_transConj {K : Subgroup M} (θ : G ≃* ↥K) (a : M) (ha2 : a * a = 1)
    (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (g : G) :
    ((θ (transConj θ a ha2 haN g) : ↥K) : M) = a * (θ g : ↥K) * a⁻¹ := by
  have : θ (transConj θ a ha2 haN g) = conjAut K a ha2 haN (θ g) := by
    simp [transConj]
  rw [this]
  rfl

@[expose] def preimage {K : Subgroup M} (θ : G ≃* ↥K) (S : Subgroup M) : Subgroup G :=
  (S.subgroupOf K).comap θ.toMonoidHom

theorem mem_preimage {K : Subgroup M} {θ : G ≃* ↥K} {S : Subgroup M} {g : G} :
    g ∈ preimage θ S ↔ ((θ g : ↥K) : M) ∈ S := Iff.rfl

theorem isSylowTwoOf_preimage {K : Subgroup M} (θ : G ≃* ↥K) {S : Subgroup M}
    (hS : IsSylowTwoOf S K) : IsSylowTwoOf (preimage θ S) ⊤ := by
  refine ⟨le_top, fun g => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hS.2.1 ⟨((θ g.1 : ↥K) : M), mem_preimage.mp g.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : ((θ g.1 : ↥K) : M) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : θ (g.1 ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by simpa using h1)
    have h3 : g.1 ^ 2 ^ k = 1 := θ.injective (h2.trans (map_one θ).symm)
    simpa using h3
  · show ¬ 2 ∣ Subgroup.relIndex (preimage θ S) ⊤
    rw [Subgroup.relIndex_top_right]
    unfold preimage
    rw [Subgroup.index_comap_of_surjective _ θ.surjective]
    exact hS.2.2

theorem exists_inner_of_sylow_cent {K S : Subgroup M} {a : M} (θ : G ≃* ↥K) (ha2 : a * a = 1)
    (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hS : IsSylowTwoOf S K) (hcent : ∀ x ∈ S, x * a = a * x)
    (hG : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → ∀ α : MulAut G, (∀ x ∈ P, α x = x) →
      ∃ p ∈ P, ∀ g, α g = p * g * p⁻¹) :
    ∃ q ∈ S, ∀ k ∈ K, a * k * a⁻¹ = q * k * q⁻¹ := by
  have hfix : ∀ x ∈ preimage θ S, transConj θ a ha2 haN x = x := by
    intro x hx
    apply θ.injective
    apply Subtype.ext
    rw [coe_transConj]
    exact mul_inv_eq_iff_eq_mul.mpr (hcent _ (mem_preimage.mp hx)).symm
  obtain ⟨p, hp, hpg⟩ := hG _ (isSylowTwoOf_preimage θ hS) _ hfix
  refine ⟨((θ p : ↥K) : M), mem_preimage.mp hp, fun k hk => ?_⟩
  have h1 := congrArg (fun g => ((θ g : ↥K) : M)) (hpg (θ.symm ⟨k, hk⟩))
  simp only [coe_transConj, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1

end Orth

end S153G93D

end CFSG.Quasithin
