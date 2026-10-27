module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgW

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] (J : HermitianForm 3 K)

@[expose] def eps (σ : Kˣ →* Kˣ) (k : Kˣ) : K := (σ k : K) * J.conj k

@[expose] noncomputable def sgn (σ : Kˣ →* Kˣ) (y : K) : K := by
  classical
  exact if hy : ∃ k : Kˣ, nrm J k = y then eps J σ (Classical.choose hy) else 1

@[expose] noncomputable def gam (F : Coord J → Coord J) (b : K) : K := by
  classical
  exact if hb : ∃ z : Coord J, z.1.2 = b ∧ z.1.1 ≠ 0 then
    (F (Classical.choose hb)).1.1 / (Classical.choose hb).1.1 else 0

@[expose] noncomputable def emm (F : Coord J → Coord J) (b : K) : K := by
  classical
  exact if hb : ∃ z : Coord J, z.1.2 = b ∧ z.1.1 ≠ 0 then (F (Classical.choose hb)).1.2 else 0

variable {J} [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem eps_sq (k : Kˣ) : eps J σ k = 1 ∨ eps J σ k = -1 := H.sigma_eq k

theorem eps_mul_self (k : Kˣ) : eps J σ k * eps J σ k = 1 := by
  rcases H.eps_sq k with e | e <;> rw [e] <;> ring

omit H [Finite K] in
theorem eps_mul (k₁ k₂ : Kˣ) : eps J σ (k₁ * k₂) = eps J σ k₁ * eps J σ k₂ := by
  simp only [eps, map_mul, Units.val_mul]; ring

omit [Finite K] in
theorem eps_of_pow_eq_one {k : Kˣ} (hk : (k : K) ^ (q + 1) = 1) : eps J σ k = 1 := by
  rw [eps, H.sigma_eq_self hk, ← nrm_def, H.nrm_eq_pow', hk]

omit [Finite K] in
theorem eps_congr {k₁ k₂ : Kˣ} (hk : nrm J k₁ = nrm J k₂) : eps J σ k₁ = eps J σ k₂ := by
  have h1 : ((k₂ * k₁⁻¹ : Kˣ) : K) ^ (q + 1) = 1 := by
    rw [← H.nrm_eq_pow', Units.val_mul, nrm_mul, Units.val_inv_eq_inv_val, nrm_inv, ← hk,
      mul_inv_cancel₀ (nrm_ne_zero J k₁.ne_zero)]
  have h2 := H.eps_of_pow_eq_one h1
  have h3 : k₂ = (k₂ * k₁⁻¹) * k₁ := by group
  rw [h3, eps_mul, h2, one_mul]

theorem eps_eq_one_of_nrm_eq_neg_one {k : Kˣ} (hk : nrm J k = -1) : eps J σ k = 1 := by
  rcases H.eps_sq k with e | e
  · exact e
  · exfalso
    have hk0 : (k : K) ≠ 0 := k.ne_zero
    have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
    have hfix : σ k = k := by
      apply Units.ext
      have h1 : (σ k : K) * J.conj k = (k : K) * J.conj k := by
        show eps J σ k = nrm J k
        rw [e, hk]
      exact mul_right_cancel₀ hck0 h1
    have := (H.σfix k).mp hfix
    rw [← H.nrm_eq_pow', hk] at this
    have h2 : (2 : K) = 0 := by linear_combination -this
    exact H.two_ne_zero' h2

omit H [Finite K] in
theorem sigma_val (k : Kˣ) : (σ k : K) = eps J σ k / J.conj k := by
  rw [eps, mul_div_assoc, div_self ((map_ne_zero J.conj).2 k.ne_zero), mul_one]

theorem conj_eps (k : Kˣ) : J.conj (eps J σ k) = eps J σ k := by
  rcases H.eps_sq k with e | e <;> rw [e] <;> simp

omit [Finite K] in
theorem sgn_nrm (k : Kˣ) : sgn J σ (nrm J k) = eps J σ k := by
  classical
  have hy : ∃ k' : Kˣ, nrm J k' = nrm J k := ⟨k, rfl⟩
  simp only [sgn, dite_eq_left hy]
  exact H.eps_congr (Classical.choose_spec hy)

theorem exists_coord {b : K} (hb : b + J.conj b ≠ 0) :
    ∃ z : Coord J, z.1.2 = b ∧ z.1.1 ≠ 0 := by
  have hy : -(b + J.conj b) ≠ 0 := neg_ne_zero.mpr hb
  have hyc : J.conj (-(b + J.conj b)) = -(b + J.conj b) := by
    rw [map_neg, map_add, conj_conj, add_comm]
  obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hy hyc
  refine ⟨⟨((k : K), b), ?_⟩, rfl, k.ne_zero⟩
  have : (k : K) * J.conj k = -(b + J.conj b) := hk
  change b + J.conj b + (k : K) * J.conj k = 0
  rw [this]; ring

omit [Finite K] in
theorem F_fst_eq {z : Coord J} (hz : z.1.1 ≠ 0) : (F z).1.1 = gam J F z.1.2 * z.1.1 := by
  classical
  have hb : ∃ w : Coord J, w.1.2 = z.1.2 ∧ w.1.1 ≠ 0 := ⟨z, rfl, hz⟩
  simp only [gam, dite_eq_left hb]
  set w := Classical.choose hb
  have hw := Classical.choose_spec hb
  have := (H.F_level hz hw.1.symm).1
  rw [div_mul_eq_mul_div, eq_div_iff hw.2]
  exact this

omit [Finite K] in
theorem F_snd_eq {z : Coord J} (hz : z.1.1 ≠ 0) : (F z).1.2 = emm J F z.1.2 := by
  classical
  have hb : ∃ w : Coord J, w.1.2 = z.1.2 ∧ w.1.1 ≠ 0 := ⟨z, rfl, hz⟩
  simp only [emm, dite_eq_left hb]
  exact (H.F_level hz (Classical.choose_spec hb).1.symm).2

omit [Finite K] in
theorem F_ne_center {z : Coord J} (hz : z.1.1 ≠ 0) : (F z).1.1 ≠ 0 := by
  intro e
  have hz1 : z ≠ 1 := fun e' => hz (by rw [e']; rfl)
  have h1 := H.F_Z (F z) (H.F_ne z hz1) e
  rw [H.F_F z hz1] at h1
  exact hz h1

omit [Finite K] in
theorem gam_ne_zero {z : Coord J} (hz : z.1.1 ≠ 0) : gam J F z.1.2 ≠ 0 := by
  intro e
  have := H.F_fst_eq hz
  rw [e, zero_mul] at this
  exact H.F_ne_center hz this

theorem gam_emm_torus {z : Coord J} (hz : z.1.1 ≠ 0) (k : Kˣ) :
    gam J F (z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹) =
        gam J F z.1.2 * eps J σ k * nrm J k ∧
      emm J F (z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹) = emm J F z.1.2 * nrm J k := by
  have hz1 : z ≠ 1 := fun e' => hz (by rw [e']; rfl)
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  set z' := hermitianTorusAction J k z with hz'def
  have hz'1 : z'.1.1 = z.1.1 * k * (J.conj (k : K))⁻¹ ^ 2 := torus_fst k z
  have hz'2 : z'.1.2 = z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹ := torus_snd k z
  have hz' : z'.1.1 ≠ 0 := by
    rw [hz'1]; exact mul_ne_zero (mul_ne_zero hz hk0) (pow_ne_zero _ (inv_ne_zero hck0))
  have hF := H.F_torus k z hz1
  rw [← hz'def] at hF
  have hσ := sigma_val (J := J) (σ := σ) k
  have hcσ : J.conj (σ k : K) = eps J σ k / k := by
    rw [hσ, map_div₀, conj_conj, H.conj_eps]
  have he := H.eps_mul_self k
  have he0 : eps J σ k ≠ 0 := by intro e; rw [e, zero_mul] at he; exact zero_ne_one he
  have hs₁ : (σ k : K) = eps J σ k * (J.conj (k : K))⁻¹ := by rw [hσ, div_eq_mul_inv]
  have hs₂ : (J.conj (σ k : K))⁻¹ = (k : K) * eps J σ k := by
    rw [hcσ, inv_div, div_eq_mul_inv]
    congr 1
    exact inv_eq_of_mul_eq_one_right he
  constructor
  · have h1 := congrArg (fun w : Coord J => w.1.1) hF
    change (F z').1.1 = (hermitianTorusAction J (σ k) (F z)).1.1 at h1
    rw [torus_fst, H.F_fst_eq hz', H.F_fst_eq hz, hz'1, hz'2, hs₂, hs₁] at h1
    have hne : z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hz hk0) (pow_ne_zero _ (inv_ne_zero hck0))
    calc gam J F (z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹)
        = gam J F (z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹) *
            (z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2) /
            (z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2) := by field_simp
      _ = gam J F z.1.2 * z.1.1 * (eps J σ k * (J.conj (k : K))⁻¹) *
            ((k : K) * eps J σ k) ^ 2 / (z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2) := by
          rw [h1]
      _ = gam J F z.1.2 * eps J σ k * nrm J k := by
          have he2 : eps J σ k ^ 2 = 1 := by rw [sq]; exact he
          rw [nrm_def, mul_pow, he2, mul_one]
          field_simp
  · have h2 := congrArg (fun w : Coord J => w.1.2) hF
    change (F z').1.2 = (hermitianTorusAction J (σ k) (F z)).1.2 at h2
    rw [torus_snd, H.F_snd_eq hz', H.F_snd_eq hz, hz'2] at h2
    rw [h2, mul_assoc, ← mul_inv, mul_comm (J.conj _), ← nrm_def, H.nrm_sigma k, inv_inv]

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
