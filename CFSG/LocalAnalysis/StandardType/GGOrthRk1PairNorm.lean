module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.StandardType

namespace OrthTorus

theorem exists_quadForm_eq_norm {K K' D : Type} [Field K] [CharP K 2] [Field K'] [CharP K' 2]
    [Algebra K K'] [AddCommGroup D] [Module K D] (σ : K' ≃+* K') (ψ : K' ≃ₗ[K] D)
    (c : D ≃ₗ[K] D) (ζ : K') (t : K) (ht : t ≠ 0) (hψ : ∀ x, ψ (ζ * x) = c (ψ x))
    (hspan : ∀ x : K', ∃ a b : K, x = algebraMap K K' a + algebraMap K K' b * ζ)
    (hζ : ζ ^ 2 + algebraMap K K' t * ζ + 1 = 0) (hσζ : σ ζ * ζ = 1)
    (hσ : ∀ a : K, σ (algebraMap K K' a) = algebraMap K K' a) (q : QuadraticForm K D)
    (hq : ∀ x, q (c x) = q x) :
    ∃ μ : K, ∀ x : K', algebraMap K K' (q (ψ x)) = algebraMap K K' μ * (σ x * x) := by
  let d : D := ψ 1
  have hψ1 : ψ ζ = c d := by simpa [d] using hψ 1
  have hpow : ζ * ζ = algebraMap K K' t * ζ + 1 := by
    have h : ζ * ζ + (algebraMap K K' t * ζ + 1) = 0 := by
      rw [pow_two] at hζ
      rwa [add_assoc] at hζ
    have := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this
  have hc2 : c (c d) = t • c d + d := by
    have h1 : c (c d) = ψ (ζ * ζ) := by rw [← hψ1, ← hψ ζ]
    rw [h1, hpow, ← Algebra.smul_def, map_add, map_smul, hψ1]
  have hqcd : q (c d) = q d := hq d
  have hqcd2 : q (c (c d)) = q d := by rw [hq (c d), hqcd]
  have hx : c (c d) = d + t • c d := by rw [hc2, add_comm]
  have h0 : q (c (c d)) = q d + q (t • c d) + QuadraticMap.polar q d (t • c d) := by
    rw [hx, QuadraticMap.map_add q]
  rw [hqcd2, QuadraticMap.map_smul q, hqcd, QuadraticMap.polar_smul_right q] at h0
  simp only [smul_eq_mul] at h0
  have hX : t * t * q d + t * QuadraticMap.polar q d (c d) = 0 := by
    have h := h0
    rw [add_assoc] at h
    exact (add_left_cancel (by rw [add_zero]; exact h)).symm
  have hfac : t * (t * q d + QuadraticMap.polar q d (c d)) = 0 := by
    rw [mul_add, ← mul_assoc]
    exact hX
  have htB : t * q d + QuadraticMap.polar q d (c d) = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h ht
    · exact h
  have hB : QuadraticMap.polar q d (c d) = t * q d := by
    have := eq_neg_of_add_eq_zero_right htB
    rwa [CharTwo.neg_eq] at this
  have hψ_ab : ∀ a b : K,
      ψ (algebraMap K K' a + algebraMap K K' b * ζ) = a • d + b • c d := by
    intro a b
    have ha : ψ (algebraMap K K' a) = a • d := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
    have hb : ψ (algebraMap K K' b * ζ) = b • c d := by
      rw [← Algebra.smul_def, map_smul, hψ1]
    rw [map_add, ha, hb]
  have hqψ : ∀ a b : K,
      q (ψ (algebraMap K K' a + algebraMap K K' b * ζ)) =
        q d * (a * a + t * a * b + b * b) := by
    intro a b
    rw [hψ_ab a b, QuadraticMap.map_add q, QuadraticMap.map_smul q, QuadraticMap.map_smul q,
      QuadraticMap.polar_smul_left q, QuadraticMap.polar_smul_right q, hqcd, hB]
    simp only [smul_eq_mul]
    ring
  have hζσ : ζ + σ ζ = algebraMap K K' t := by
    have hmul : ζ + algebraMap K K' t + σ ζ = 0 := by
      have h := congrArg (fun z => σ ζ * z) hζ
      simp only [mul_add, mul_one, mul_zero, pow_two] at h
      have h1 : σ ζ * (ζ * ζ) = ζ := by rw [← mul_assoc, hσζ, one_mul]
      have h2 : σ ζ * (algebraMap K K' t * ζ) = algebraMap K K' t := by
        rw [show σ ζ * (algebraMap K K' t * ζ)
              = algebraMap K K' t * (σ ζ * ζ) by ring, hσζ, mul_one]
      rw [h1, h2] at h
      exact h
    have h' : (ζ + σ ζ) + algebraMap K K' t = 0 := by
      rw [← hmul]; ring
    have := eq_neg_of_add_eq_zero_left h'
    rwa [CharTwo.neg_eq] at this
  have hσx : ∀ a b : K,
      σ (algebraMap K K' a + algebraMap K K' b * ζ)
        = algebraMap K K' a + algebraMap K K' b * σ ζ := by
    intro a b
    rw [map_add, map_mul, hσ a, hσ b]
  have hnorm : ∀ a b : K,
      σ (algebraMap K K' a + algebraMap K K' b * ζ) *
          (algebraMap K K' a + algebraMap K K' b * ζ)
        = algebraMap K K' (a * a + t * a * b + b * b) := by
    intro a b
    rw [hσx a b]
    have hexp : (algebraMap K K' a + algebraMap K K' b * σ ζ) *
          (algebraMap K K' a + algebraMap K K' b * ζ)
        = algebraMap K K' a * algebraMap K K' a
          + algebraMap K K' a * algebraMap K K' b * (ζ + σ ζ)
          + algebraMap K K' b * algebraMap K K' b * (σ ζ * ζ) := by
      ring
    rw [hexp, hζσ, hσζ, mul_one]
    simp only [map_add, map_mul]
    ring
  refine ⟨q d, ?_⟩
  intro x
  obtain ⟨a, b, rfl⟩ := hspan x
  rw [hqψ a b, hnorm a b, map_mul]

end OrthTorus

end CFSG.StandardType

end
