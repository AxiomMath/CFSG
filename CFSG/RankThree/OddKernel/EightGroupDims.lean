module

public import CFSG.RankThree.OddKernel.InvolutionDims
public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.RankThree.OddKernel

open Module

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

theorem fixSpace_comp_inf (g ρ : W →ₗ[K] W) (X : Submodule K W) :
    X ⊓ fixSpace (g ∘ₗ ρ) ⊓ fixSpace ρ = X ⊓ fixSpace ρ ⊓ fixSpace g ∧
      X ⊓ fixSpace (g ∘ₗ ρ) ⊓ negSpace ρ = X ⊓ negSpace ρ ⊓ negSpace g := by
  constructor
  · ext v
    simp only [Submodule.mem_inf, mem_fixSpace, LinearMap.comp_apply]
    constructor
    · rintro ⟨⟨hv, h1⟩, h2⟩
      rw [h2] at h1
      exact ⟨⟨hv, h2⟩, h1⟩
    · rintro ⟨⟨hv, h2⟩, h1⟩
      exact ⟨⟨hv, by rw [h2, h1]⟩, h2⟩
  · ext v
    simp only [Submodule.mem_inf, mem_fixSpace, mem_negSpace, LinearMap.comp_apply]
    constructor
    · rintro ⟨⟨hv, h1⟩, h2⟩
      rw [h2, map_neg] at h1
      exact ⟨⟨hv, h2⟩, neg_eq_iff_eq_neg.mp h1⟩
    · rintro ⟨⟨hv, h2⟩, h1⟩
      exact ⟨⟨hv, by rw [h2, map_neg, h1, neg_neg]⟩, h2⟩

theorem sum_finrank_fix_eight [FiniteDimensional K W] (h2 : (2 : K) ≠ 0) (σ τ ρ : W →ₗ[K] W)
    (hσ : ∀ w, σ (σ w) = w) (hτ : ∀ w, τ (τ w) = w) (hρ : ∀ w, ρ (ρ w) = w)
    (hστ : ∀ w, σ (τ w) = τ (σ w)) (hσρ : ∀ w, σ (ρ w) = ρ (σ w))
    (hτρ : ∀ w, τ (ρ w) = ρ (τ w)) (X : Submodule K W) (hXσ : ∀ x ∈ X, σ x ∈ X)
    (hXτ : ∀ x ∈ X, τ x ∈ X) (hXρ : ∀ x ∈ X, ρ x ∈ X) :
    finrank K ↥(X ⊓ fixSpace σ) + finrank K ↥(X ⊓ fixSpace τ) +
        finrank K ↥(X ⊓ fixSpace (σ ∘ₗ τ)) + finrank K ↥(X ⊓ fixSpace ρ) +
        finrank K ↥(X ⊓ fixSpace (σ ∘ₗ ρ)) + finrank K ↥(X ⊓ fixSpace (τ ∘ₗ ρ)) +
        finrank K ↥(X ⊓ fixSpace ((σ ∘ₗ τ) ∘ₗ ρ)) =
      3 * finrank K X + 4 * finrank K ↥(X ⊓ fixSpace ρ ⊓ (fixSpace σ ⊓ fixSpace τ)) := by
  have hστi : ∀ w, (σ ∘ₗ τ) ((σ ∘ₗ τ) w) = w := fun w => by
    simp only [LinearMap.comp_apply]
    rw [hστ (σ (τ w)), hσ, hτ]
  have hστρ : ∀ w, (σ ∘ₗ τ) (ρ w) = ρ ((σ ∘ₗ τ) w) := fun w => by
    simp only [LinearMap.comp_apply]
    rw [hτρ, hσρ]
  have hXστ : ∀ x ∈ X, (σ ∘ₗ τ) x ∈ X := fun x hx => hXσ _ (hXτ x hx)
  have hinvp : ∀ g : W →ₗ[K] W, (∀ x ∈ X, g x ∈ X) → (∀ w, g (ρ w) = ρ (g w)) →
      ∀ x ∈ X ⊓ fixSpace ρ, g x ∈ X ⊓ fixSpace ρ := by
    rintro g hgX hgρ x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_fixSpace] at hx'
    exact ⟨hgX x hx, by rw [SetLike.mem_coe, mem_fixSpace, ← hgρ, hx']⟩
  have hinvm : ∀ g : W →ₗ[K] W, (∀ x ∈ X, g x ∈ X) → (∀ w, g (ρ w) = ρ (g w)) →
      ∀ x ∈ X ⊓ negSpace ρ, g x ∈ X ⊓ negSpace ρ := by
    rintro g hgX hgρ x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_negSpace] at hx'
    exact ⟨hgX x hx, by rw [SetLike.mem_coe, mem_negSpace, ← hgρ, hx', map_neg]⟩
  have hinvF : ∀ g : W →ₗ[K] W, (∀ w, g (ρ w) = ρ (g w)) →
      ∀ x ∈ X ⊓ fixSpace g, ρ x ∈ X ⊓ fixSpace g := by
    rintro g hgρ x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_fixSpace] at hx'
    exact ⟨hXρ x hx, by rw [SetLike.mem_coe, mem_fixSpace, hgρ, hx']⟩
  have hinvFρ : ∀ g : W →ₗ[K] W, (∀ w, g (ρ w) = ρ (g w)) →
      ∀ x ∈ X ⊓ fixSpace (g ∘ₗ ρ), ρ x ∈ X ⊓ fixSpace (g ∘ₗ ρ) := by
    rintro g hgρ x ⟨hx, hx'⟩
    rw [SetLike.mem_coe, mem_fixSpace, LinearMap.comp_apply] at hx'
    refine ⟨hXρ x hx, ?_⟩
    rw [SetLike.mem_coe, mem_fixSpace, LinearMap.comp_apply, hgρ (ρ x), hx']
  have hX := finrank_eq_fix_add_neg h2 ρ hρ X hXρ
  have hA : ∀ g : W →ₗ[K] W, (∀ w, g (ρ w) = ρ (g w)) →
      finrank K ↥(X ⊓ fixSpace g) =
        finrank K ↥(X ⊓ fixSpace ρ ⊓ fixSpace g) +
          finrank K ↥(X ⊓ negSpace ρ ⊓ fixSpace g) := by
    intro g hgρ
    have h := finrank_eq_fix_add_neg h2 ρ hρ _ (hinvF g hgρ)
    rw [inf_right_comm X (fixSpace g) (fixSpace ρ), inf_right_comm X (fixSpace g)] at h
    exact h
  have hB : ∀ g : W →ₗ[K] W, (∀ w, g (ρ w) = ρ (g w)) →
      finrank K ↥(X ⊓ fixSpace (g ∘ₗ ρ)) =
        finrank K ↥(X ⊓ fixSpace ρ ⊓ fixSpace g) +
          finrank K ↥(X ⊓ negSpace ρ ⊓ negSpace g) := by
    intro g hgρ
    have h := finrank_eq_fix_add_neg h2 ρ hρ _ (hinvFρ g hgρ)
    rw [(fixSpace_comp_inf g ρ X).1, (fixSpace_comp_inf g ρ X).2] at h
    exact h
  have hC : ∀ g : W →ₗ[K] W, (∀ w, g (g w) = w) → (∀ x ∈ X, g x ∈ X) →
      (∀ w, g (ρ w) = ρ (g w)) →
      finrank K ↥(X ⊓ negSpace ρ) = finrank K ↥(X ⊓ negSpace ρ ⊓ fixSpace g) +
        finrank K ↥(X ⊓ negSpace ρ ⊓ negSpace g) := by
    intro g hg hgX hgρ
    exact finrank_eq_fix_add_neg h2 g hg _ (hinvm g hgX hgρ)
  obtain ⟨hpX, hp1, hp2, hp3⟩ := finrank_four_group h2 σ τ hσ hτ hστ (X ⊓ fixSpace ρ)
    (hinvp σ hXσ hσρ) (hinvp τ hXτ hτρ)
  have hσp := hA σ hσρ
  have hτp := hA τ hτρ
  have hστp := hA (σ ∘ₗ τ) hστρ
  have hσq := hB σ hσρ
  have hτq := hB τ hτρ
  have hστq := hB (σ ∘ₗ τ) hστρ
  have hσm := hC σ hσ hXσ hσρ
  have hτm := hC τ hτ hXτ hτρ
  have hστm := hC (σ ∘ₗ τ) hστi hXστ hστρ
  omega

theorem det_eq_neg_one_pow_of_involution [FiniteDimensional K W] (g : W →ₗ[K] W)
    (hg : ∀ w, g (g w) = w) :
    LinearMap.det g = (-1) ^ (finrank K W - finrank K (fixSpace g)) := by
  have hle : fixSpace g ≤ (fixSpace g).comap g := fun x hx => by
    rw [Submodule.mem_comap, mem_fixSpace]
    rw [mem_fixSpace] at hx
    rw [hx, hx]
  have hdet := LinearMap.det_eq_det_mul_det (fixSpace g) g hle
  have hres : g.restrict hle = LinearMap.id := by
    ext x
    exact mem_fixSpace.1 x.2
  have hquot : (fixSpace g).mapQ (fixSpace g) g hle = (-1 : K) • LinearMap.id := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply, neg_one_smul]
    rw [← Submodule.Quotient.mk_neg, Submodule.Quotient.eq, sub_neg_eq_add, mem_fixSpace,
      map_add, hg, add_comm]
  rw [hdet, hres, hquot, LinearMap.det_id, one_mul, LinearMap.det_smul, LinearMap.det_id, mul_one]
  congr 1
  have := Submodule.finrank_quotient_add_finrank (fixSpace g)
  omega

theorem eq_neg_of_fixSpace_eq_bot [FiniteDimensional K W] (h2 : (2 : K) ≠ 0)
    (g : W →ₗ[K] W) (hg : ∀ w, g (g w) = w) (h0 : finrank K (fixSpace g) = 0) (w : W) :
    g w = -w := by
  have h := finrank_eq_fix_add_neg h2 g hg ⊤ fun x _ => Submodule.mem_top
  rw [top_inf_eq, top_inf_eq, finrank_top, h0, zero_add] at h
  have hN : negSpace g = ⊤ := Submodule.eq_top_of_finrank_eq h.symm
  exact mem_negSpace.1 (hN ▸ Submodule.mem_top)

end CFSG.RankThree.OddKernel
