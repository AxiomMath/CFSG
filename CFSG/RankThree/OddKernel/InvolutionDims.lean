module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.OddKernel

open Module

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

@[expose] def fixSpace (σ : W →ₗ[K] W) : Submodule K W := LinearMap.ker (σ - LinearMap.id)

@[expose] def negSpace (σ : W →ₗ[K] W) : Submodule K W := LinearMap.ker (σ + LinearMap.id)

theorem mem_fixSpace {σ : W →ₗ[K] W} {v : W} : v ∈ fixSpace σ ↔ σ v = v := by
  rw [fixSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_negSpace {σ : W →ₗ[K] W} {v : W} : v ∈ negSpace σ ↔ σ v = -v := by
  rw [negSpace, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]

theorem finrank_eq_fix_add_neg [FiniteDimensional K W] (h2 : (2 : K) ≠ 0) (σ : W →ₗ[K] W)
    (hσ : ∀ w, σ (σ w) = w)
    (X : Submodule K W) (hX : ∀ x ∈ X, σ x ∈ X) :
    finrank K X = finrank K ↥(X ⊓ fixSpace σ) + finrank K ↥(X ⊓ negSpace σ) := by
  set A := X ⊓ fixSpace σ with hA
  set B := X ⊓ negSpace σ with hB
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨-, hv1⟩, ⟨-, hv2⟩⟩
    rw [SetLike.mem_coe, mem_fixSpace] at hv1
    rw [SetLike.mem_coe, mem_negSpace] at hv2
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      calc v + v = σ v + v := by rw [hv1]
        _ = 0 := by rw [hv2, neg_add_cancel]
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.1 h2v).resolve_left h2
  have hsup : A ⊔ B = X := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    have hx1 : (2 : K)⁻¹ • (x + σ x) ∈ A := by
      refine ⟨X.smul_mem _ (X.add_mem hx (hX x hx)), ?_⟩
      rw [SetLike.mem_coe, mem_fixSpace, map_smul, map_add, hσ, add_comm]
    have hx2 : (2 : K)⁻¹ • (x - σ x) ∈ B := by
      refine ⟨X.smul_mem _ (X.sub_mem hx (hX x hx)), ?_⟩
      rw [SetLike.mem_coe, mem_negSpace, map_smul, map_sub, hσ, ← smul_neg, neg_sub]
    have hx' : x = (2 : K)⁻¹ • (x + σ x) + (2 : K)⁻¹ • (x - σ x) := by
      rw [← smul_add, show x + σ x + (x - σ x) = (2 : K) • x by rw [two_smul]; abel, smul_smul,
        inv_mul_cancel₀ h2, one_smul]
    rw [hx']
    exact Submodule.add_mem_sup hx1 hx2
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, hAB, finrank_bot, add_zero] at this
  exact this

theorem finrank_four_group [FiniteDimensional K W] (h2 : (2 : K) ≠ 0) (σ τ : W →ₗ[K] W)
    (hσ : ∀ w, σ (σ w) = w)
    (hτ : ∀ w, τ (τ w) = w) (hστ : ∀ w, σ (τ w) = τ (σ w)) (X : Submodule K W)
    (hXσ : ∀ x ∈ X, σ x ∈ X) (hXτ : ∀ x ∈ X, τ x ∈ X) :
    finrank K X = finrank K ↥(X ⊓ (fixSpace σ ⊓ fixSpace τ)) +
        finrank K ↥(X ⊓ (fixSpace σ ⊓ negSpace τ)) +
        finrank K ↥(X ⊓ (negSpace σ ⊓ fixSpace τ)) +
        finrank K ↥(X ⊓ (negSpace σ ⊓ negSpace τ)) ∧
      finrank K ↥(X ⊓ fixSpace σ) = finrank K ↥(X ⊓ (fixSpace σ ⊓ fixSpace τ)) +
        finrank K ↥(X ⊓ (fixSpace σ ⊓ negSpace τ)) ∧
      finrank K ↥(X ⊓ fixSpace τ) = finrank K ↥(X ⊓ (fixSpace σ ⊓ fixSpace τ)) +
        finrank K ↥(X ⊓ (negSpace σ ⊓ fixSpace τ)) ∧
      finrank K ↥(X ⊓ fixSpace (σ ∘ₗ τ)) = finrank K ↥(X ⊓ (fixSpace σ ⊓ fixSpace τ)) +
        finrank K ↥(X ⊓ (negSpace σ ⊓ negSpace τ)) := by
  have hFσ : ∀ x ∈ X ⊓ fixSpace σ, τ x ∈ X ⊓ fixSpace σ := by
    rintro x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_fixSpace] at hx'
    exact ⟨hXτ x hx, by rw [SetLike.mem_coe, mem_fixSpace, hστ, hx']⟩
  have hNσ : ∀ x ∈ X ⊓ negSpace σ, τ x ∈ X ⊓ negSpace σ := by
    rintro x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_negSpace] at hx'
    exact ⟨hXτ x hx, by rw [SetLike.mem_coe, mem_negSpace, hστ, hx', map_neg]⟩
  have hFτ : ∀ x ∈ X ⊓ fixSpace τ, σ x ∈ X ⊓ fixSpace τ := by
    rintro x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_fixSpace] at hx'
    exact ⟨hXσ x hx, by rw [SetLike.mem_coe, mem_fixSpace, ← hστ, hx']⟩
  have hFστ : ∀ x ∈ X ⊓ fixSpace (σ ∘ₗ τ), σ x ∈ X ⊓ fixSpace (σ ∘ₗ τ) := by
    rintro x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_fixSpace, LinearMap.comp_apply] at hx'
    refine ⟨hXσ x hx, ?_⟩
    rw [SetLike.mem_coe, mem_fixSpace, LinearMap.comp_apply, ← hστ, hσ]
    calc τ x = σ (σ (τ x)) := (hσ _).symm
      _ = σ x := by rw [hx']
  have h1 := finrank_eq_fix_add_neg h2 σ hσ X hXσ
  have h2' := finrank_eq_fix_add_neg h2 τ hτ _ hFσ
  have h3 := finrank_eq_fix_add_neg h2 τ hτ _ hNσ
  have h4 := finrank_eq_fix_add_neg h2 σ hσ _ hFτ
  have h5 := finrank_eq_fix_add_neg h2 σ hσ _ hFστ
  have e1 : X ⊓ fixSpace τ ⊓ fixSpace σ = X ⊓ (fixSpace σ ⊓ fixSpace τ) := by
    rw [inf_assoc, inf_comm (fixSpace τ)]
  have e2 : X ⊓ fixSpace τ ⊓ negSpace σ = X ⊓ (negSpace σ ⊓ fixSpace τ) := by
    rw [inf_assoc, inf_comm (fixSpace τ)]
  have e3 : X ⊓ fixSpace (σ ∘ₗ τ) ⊓ fixSpace σ = X ⊓ (fixSpace σ ⊓ fixSpace τ) := by
    ext v
    simp only [Submodule.mem_inf, mem_fixSpace, LinearMap.comp_apply]
    constructor
    · rintro ⟨⟨hv, hv1⟩, hv2⟩
      refine ⟨hv, hv2, ?_⟩
      calc τ v = σ (σ (τ v)) := (hσ _).symm
        _ = v := by rw [hv1, hv2]
    · rintro ⟨hv, hv2, hv3⟩
      exact ⟨⟨hv, by rw [hv3, hv2]⟩, hv2⟩
  have e4 : X ⊓ fixSpace (σ ∘ₗ τ) ⊓ negSpace σ = X ⊓ (negSpace σ ⊓ negSpace τ) := by
    ext v
    simp only [Submodule.mem_inf, mem_fixSpace, mem_negSpace, LinearMap.comp_apply]
    constructor
    · rintro ⟨⟨hv, hv1⟩, hv2⟩
      refine ⟨hv, hv2, ?_⟩
      calc τ v = σ (σ (τ v)) := (hσ _).symm
        _ = -v := by rw [hv1, hv2]
    · rintro ⟨hv, hv2, hv3⟩
      exact ⟨⟨hv, by rw [hv3, map_neg, hv2, neg_neg]⟩, hv2⟩
  rw [e1, e2] at h4
  rw [e3, e4] at h5
  rw [inf_assoc, inf_assoc] at h2'
  rw [inf_assoc, inf_assoc] at h3
  refine ⟨?_, h2', h4, h5⟩
  rw [h1, h2', h3]
  ring

end CFSG.RankThree.OddKernel
