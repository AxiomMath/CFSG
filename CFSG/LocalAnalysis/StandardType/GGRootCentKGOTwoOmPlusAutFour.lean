module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityRoots
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor

public section

namespace CFSG.StandardType.KGOm

open CFSG.StandardType.Triality

private theorem theta_pow_X8 {K : Type} [Field K] [Finite K] [CharP K 2] (k : ℕ) :
    ∀ {γ : Fin 4 → ℤ}, γ ∈ rootsD4 → ∀ b : K,
      ((theta : MulAut (Om8 K)) ^ k) (X8 γ b) = X8 ((⇑tri)^[k] γ) b := by
  induction k with
  | zero =>
      intro γ hγ b
      rw [pow_zero, MulAut.one_apply, Function.iterate_zero_apply]
  | succ k ih =>
      intro γ hγ b
      rw [pow_succ, MulAut.mul_apply, theta_X8 hγ, ih (tri_mem_roots hγ),
        Function.iterate_succ_apply]

theorem exists_conj_tri_of_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type*} [Group G] {ψ : Triality.Sp8 K →* G} (hψ : Function.Injective ψ) {a : G}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (γ : Triality.Sp8 K) (c : Triality.Sp8 K →* Triality.Sp8 K) (k : ℕ) (ε : Bool)
      (τ : K ≃+* K),
      (∀ z, a * ψ z * a⁻¹ = ψ (γ * c z * γ⁻¹)) ∧
      ∀ δ ∈ Triality.rootsD4, ∀ b : K,
        c (Triality.xr δ b) =
          Triality.xr ((⇑Triality.tri)^[k] (if ε then Triality.refl0 δ else δ)) (τ b) := by
  classical
  let Θ : Om8 K ≃* ψ.range := modelEquiv8.symm.trans (MonoidHom.ofInjective hψ)
  let cAut : MulAut ψ.range := CFSG.LocalAnalysis.ComponentInitial.conjAut ψ.range ha
  let α : MulAut (Om8 K) := (Θ.trans cAut).trans Θ.symm
  obtain ⟨ι, hι, k, c₀, hc₀, hα⟩ := exists_inner_mul_theta_pow_mul (K := K) α
  change ι ∈ (MulAut.conj : Om8 K →* MulAut (Om8 K)).range at hι
  obtain ⟨γ', hγ'⟩ := MonoidHom.mem_range.1 hι
  let γ : Sp8 K := modelEquiv8.symm γ'
  let c : Sp8 K →* Sp8 K :=
    modelEquiv8.symm.toMonoidHom.comp
      (((theta : MulAut (Om8 K)) ^ k * c₀).toMonoidHom.comp modelEquiv8.toMonoidHom)
  have hΘ : ∀ x : Sp8 K, Θ (modelEquiv8 x) = ⟨ψ x, ⟨x, rfl⟩⟩ := by
    intro x
    have h : Θ (modelEquiv8 x) = MonoidHom.ofInjective hψ x := by
      simp [Θ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h]
    exact Subtype.ext (MonoidHom.ofInjective_apply hψ)
  have hconj : ∀ z : Sp8 K, a * ψ z * a⁻¹ = ψ (γ * c z * γ⁻¹) := by
    intro z
    have hmem : a * ψ z * a⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp ha (ψ z)).mp ⟨z, rfl⟩
    have h1 : Θ (α (modelEquiv8 z)) = ⟨a * ψ z * a⁻¹, hmem⟩ := by
      change Θ (Θ.symm (cAut (Θ (modelEquiv8 z)))) = _
      rw [hΘ z, MulEquiv.apply_symm_apply]
      exact Subtype.ext (CFSG.LocalAnalysis.ComponentInitial.coe_conjAut ha ⟨ψ z, ⟨z, rfl⟩⟩)
    have h2 : Θ (α (modelEquiv8 z)) = ⟨ψ (γ * c z * γ⁻¹), ⟨_, rfl⟩⟩ := by
      have hγz : modelEquiv8 (γ * c z * γ⁻¹) =
          γ' * (((theta : MulAut (Om8 K)) ^ k * c₀) (modelEquiv8 z)) * γ'⁻¹ := by
        simp [γ, c, map_mul, map_inv]
      calc Θ (α (modelEquiv8 z)) =
            Θ (MulAut.conj γ'
              (((theta : MulAut (Om8 K)) ^ k * c₀) (modelEquiv8 z))) := by
            rw [hα, ← hγ']
            rfl
        _ = Θ (modelEquiv8 (γ * c z * γ⁻¹)) := by
            rw [MulAut.conj_apply, ← hγz]
        _ = ⟨ψ (γ * c z * γ⁻¹), ⟨_, rfl⟩⟩ := hΘ _
    exact congrArg Subtype.val (h1.symm.trans h2)
  rw [AutOm.mem_plusCompl] at hc₀
  rcases hc₀ with ⟨τ, hc₀ | hc₀⟩
  · have hc : c = modelEquiv8.symm.toMonoidHom.comp
        ((((theta : MulAut (Om8 K)) ^ k * AutOm.fieldAutP 4 τ).toMonoidHom).comp
          modelEquiv8.toMonoidHom) := by
      rw [← hc₀]
    refine ⟨γ, modelEquiv8.symm.toMonoidHom.comp
      ((((theta : MulAut (Om8 K)) ^ k * AutOm.fieldAutP 4 τ).toMonoidHom).comp
        modelEquiv8.toMonoidHom), k, false, τ, ?_, ?_⟩
    · rw [← hc]
      exact hconj
    · intro δ hδ b
      change modelEquiv8.symm
        (((theta : MulAut (Om8 K)) ^ k * AutOm.fieldAutP 4 τ)
          (modelEquiv8 (xr δ b))) = _
      rw [show modelEquiv8 (xr δ b) = X8 δ b from rfl, MulAut.mul_apply,
        fieldAutP_X8 τ hδ b, theta_pow_X8 k hδ (τ b),
        show modelEquiv8.symm (X8 ((⇑tri)^[k] δ) (τ b)) =
          xr ((⇑tri)^[k] δ) (τ b) from
            MulEquiv.symm_apply_apply modelEquiv8 (xr ((⇑tri)^[k] δ) (τ b))]
      simp
  · have hc : c = modelEquiv8.symm.toMonoidHom.comp
        ((((theta : MulAut (Om8 K)) ^ k *
          (AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 τ)).toMonoidHom).comp
          modelEquiv8.toMonoidHom) := by
      rw [← hc₀]
    refine ⟨γ, modelEquiv8.symm.toMonoidHom.comp
      ((((theta : MulAut (Om8 K)) ^ k *
        (AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 τ)).toMonoidHom).comp
        modelEquiv8.toMonoidHom), k, true, τ, ?_, ?_⟩
    · rw [← hc]
      exact hconj
    · intro δ hδ b
      change modelEquiv8.symm
        (((theta : MulAut (Om8 K)) ^ k *
          (AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 τ))
            (modelEquiv8 (xr δ b))) = _
      rw [show modelEquiv8 (xr δ b) = X8 δ b from rfl, MulAut.mul_apply, MulAut.mul_apply,
        fieldAutP_X8 τ hδ b, plusRefl_X8 hδ (τ b),
        theta_pow_X8 k (refl0_mem_roots hδ) (τ b),
        show modelEquiv8.symm (X8 ((⇑tri)^[k] (refl0 δ)) (τ b)) =
          xr ((⇑tri)^[k] (refl0 δ)) (τ b) from
            MulEquiv.symm_apply_apply modelEquiv8 (xr ((⇑tri)^[k] (refl0 δ)) (τ b))]
      simp

end CFSG.StandardType.KGOm
