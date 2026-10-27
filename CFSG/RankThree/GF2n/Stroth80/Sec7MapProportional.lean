module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_map_eq_smul_of_form_eq {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (f : LinearMap.BilinForm K E) (_hf : f.Nondegenerate)
    (_hr : f.IsRefl) (U : Submodule K E) (ψ ψ' : E →ₗ[K] E)
    (hr1 : LinearMap.range ψ = U) (hr2 : LinearMap.range ψ' = U)
    (hk2 : LinearMap.ker ψ' = f.orthogonal U) (μ : K) (_hμ : μ ≠ 0)
    (hform : ∀ x ∈ U, ∀ c c' : E, ψ' c' = ψ c → f x c' = μ * f x c) :
    ∀ c : E, ψ c = μ • ψ' c := by
  intro c
  have hmem : ψ c ∈ LinearMap.range ψ' := by
    rw [hr2, ← hr1]
    exact LinearMap.mem_range_self ψ c
  obtain ⟨c', hc'⟩ := LinearMap.mem_range.mp hmem
  have hortho : c' - μ • c ∈ f.orthogonal U := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have h1 := hform x hx c c' hc'
    rw [map_sub, LinearMap.map_smul, smul_eq_mul, h1, sub_self]
  have hker : c' - μ • c ∈ LinearMap.ker ψ' := by
    rw [hk2]
    exact hortho
  have h2 : ψ' (c' - μ • c) = 0 := LinearMap.mem_ker.mp hker
  rw [map_sub, LinearMap.map_smul, hc'] at h2
  exact sub_eq_zero.mp h2

theorem sec7_conj_semilinear_linear {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (σ : K ≃+* K) (g : E ≃+ E) (hg : ∀ (c : K) (e : E), g (c • e) = σ c • g e)
    (ψ : E →ₗ[K] E) :
    ∃ ψx : E →ₗ[K] E, (∀ e, ψx e = g (ψ (g.symm e))) ∧
      ∀ (lam : K) (e : E), g (e + lam • ψ e) = g e + σ lam • ψx (g e) := by
  have hgs : ∀ (c : K) (e : E), g.symm (c • e) = σ.symm c • g.symm e := by
    intro c e
    apply g.injective
    rw [g.apply_symm_apply, hg, σ.apply_symm_apply, g.apply_symm_apply]
  obtain ⟨ψx, hψx⟩ : ∃ ψx : E →ₗ[K] E, ∀ e, ψx e = g (ψ (g.symm e)) := by
    refine ⟨{ toFun := fun e => g (ψ (g.symm e)), map_add' := ?_, map_smul' := ?_ },
      fun e => rfl⟩
    · intro x y
      simp only [map_add]
    · intro c e
      simp only [RingHom.id_apply]
      rw [hgs, LinearMap.map_smul, hg, σ.apply_symm_apply]
  refine ⟨ψx, hψx, fun lam e => ?_⟩
  rw [hψx, g.symm_apply_apply, map_add, hg]

end CFSG.RankThree.GF2n.Stroth80
