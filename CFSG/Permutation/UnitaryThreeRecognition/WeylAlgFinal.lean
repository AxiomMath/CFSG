module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgSgn

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem nrm_conj (x : K) : nrm J (J.conj x) = nrm J x := by
  rw [nrm_def, nrm_def, conj_conj, mul_comm]

variable [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem exists_weyl_normalization :
    ∃ k₀ : Kˣ, ∀ c : Coord J, c ≠ 1 →
      hermitianTorusAction J k₀ (F (hermitianTorusAction J k₀⁻¹ c)) = weylCoord J c := by
  classical
  obtain ⟨κ, hκ0, hκc, hκF⟩ := H.exists_F_center
  obtain ⟨c₀, hc₀0, hgam⟩ := H.gam_eq
  obtain ⟨c₁, hc₁0, hc₁⟩ := H.exists_trace_zero
  obtain ⟨hsgn, hc₀sq⟩ := H.sgn_eq_one hκF hκ0 hκc hc₀0 hgam hc₁0 hc₁
  have hsgn' : ∀ y : K, sgn J σ y = 1 := by
    intro y
    by_cases hy : ∃ k : Kˣ, nrm J k = y
    · obtain ⟨k, rfl⟩ := hy
      exact hsgn _ (nrm_ne_zero J k.ne_zero) (conj_nrm J _)
    · rw [sgn, dite_eq_right hy]
  have hgam' : ∀ b : K, b + J.conj b ≠ 0 → gam J F b = c₀ / J.conj b := by
    intro b hb; rw [hgam b hb, hsgn', mul_one]
  obtain ⟨z₂, hz₂b, hz₂a⟩ := exists_coord_two (J := J)
  have hz₂ : z₂.1.1 ≠ 0 := by rw [hz₂a]; exact H.two_ne_zero'
  have hρ := (H.emm_eq hκF hκ0 hκc hc₀0 hgam hc₁0 hc₁ hz₂).2 c₁ hc₁0 hc₁
  simp only [hsgn', mul_one] at hρ
  have hNθ : nrm J (c₁ * theta h c₁ hc₁) = κ := by
    have hNh := H.nrm_h_center hκF hκ0 hκc hc₁0 hc₁
    have hh0 : (h (zc c₁ hc₁) : K) ≠ 0 := (h _).ne_zero
    have hNh0 : nrm J (h (zc c₁ hc₁) : K) ≠ 0 := nrm_ne_zero J hh0
    rw [theta, nrm_mul, nrm_mul, inv_pow, nrm_inv, sq (J.conj _), nrm_mul, nrm_conj, hNh,
      nrm_def J c₁, hc₁]
    field_simp
  have hNc₀ : nrm J c₀ = κ := by
    have := congrArg (nrm J) hρ
    rw [nrm_mul, hNθ, nrm_def J (-κ), map_neg, hκc] at this
    have : nrm J c₀ * κ = κ * κ := by linear_combination this
    exact mul_right_cancel₀ hκ0 this
  have hcc₀ : J.conj c₀ = c₀ := by
    have : c₀ * J.conj c₀ = c₀ * c₀ := by rw [← nrm_def, hNc₀, ← hc₀sq, sq]
    exact mul_left_cancel₀ hc₀0 this
  obtain ⟨k₀, hk₀⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega)
    (neg_ne_zero.mpr hc₀0) (by rw [map_neg, hcc₀])
  have hk₀' : (k₀ : K) * J.conj (k₀ : K) = -c₀ := hk₀
  have hk0 : (k₀ : K) ≠ 0 := k₀.ne_zero
  have hck0 : J.conj (k₀ : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  refine ⟨k₀, fun c hc => ?_⟩
  set c' := hermitianTorusAction J k₀⁻¹ c with hc'def
  have hc'1 : c'.1.1 = c.1.1 * (J.conj (k₀ : K)) ^ 2 / k₀ := by
    rw [hc'def, torus_fst, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]; field_simp
  have hc'2 : c'.1.2 = -c₀ * c.1.2 := by
    rw [hc'def, torus_snd, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, inv_inv, ← hk₀']
    ring
  have hcb : c.1.2 ≠ 0 := coord_snd_ne_zero J hc
  have hc'ne : c' ≠ 1 := by
    intro e
    have := congrArg (fun v : Coord J => v.1.2) e
    change c'.1.2 = 0 at this
    rw [hc'2] at this
    exact mul_ne_zero (neg_ne_zero.mpr hc₀0) hcb this
  apply coord_ext
  · rw [torus_fst, weylCoord_val]
    by_cases ha : c.1.1 = 0
    · have hc'a : c'.1.1 = 0 := by rw [hc'1, ha]; ring
      rw [(hκF c' hc'ne hc'a).1, ha]; ring
    · have hc'a : c'.1.1 ≠ 0 := by
        rw [hc'1]; exact div_ne_zero (mul_ne_zero ha (pow_ne_zero _ hck0)) hk0
      have htr := tr_ne_zero_of_fst hc'a
      rw [H.F_fst_eq hc'a, hgam' _ htr, hc'2, hc'1, map_mul, map_neg, hcc₀]
      have hcb' : J.conj c.1.2 ≠ 0 := (map_ne_zero J.conj).2 hcb
      field_simp
  · rw [torus_snd, weylCoord_val]
    by_cases ha : c.1.1 = 0
    · have hc'a : c'.1.1 = 0 := by rw [hc'1, ha]; ring
      rw [(hκF c' hc'ne hc'a).2, hc'2, ← hc₀sq]
      change c₀ ^ 2 / (-c₀ * c.1.2) * (J.conj (k₀ : K))⁻¹ * (k₀ : K)⁻¹ = c.1.2⁻¹
      have : (J.conj (k₀ : K))⁻¹ * (k₀ : K)⁻¹ = (-c₀)⁻¹ := by
        rw [← mul_inv, mul_comm, hk₀']
      rw [mul_assoc, this]
      field_simp
    · have hc'a : c'.1.1 ≠ 0 := by
        rw [hc'1]; exact div_ne_zero (mul_ne_zero ha (pow_ne_zero _ hck0)) hk0
      rw [H.F_snd_eq hc'a, (H.emm_eq hκF hκ0 hκc hc₀0 hgam hc₁0 hc₁ hc'a).1, hc'2, ← hc₀sq]
      change c₀ ^ 2 / (-c₀ * c.1.2) * (J.conj (k₀ : K))⁻¹ * (k₀ : K)⁻¹ = c.1.2⁻¹
      have : (J.conj (k₀ : K))⁻¹ * (k₀ : K)⁻¹ = (-c₀)⁻¹ := by
        rw [← mul_inv, mul_comm, hk₀']
      rw [mul_assoc, this]
      field_simp

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
