module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgT

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] (J : HermitianForm 3 K)

@[expose] def nn (b : K) : K := -(b * J.conj b) / (b + J.conj b)

theorem conj_nn (b : K) : J.conj (nn J b) = nn J b := by
  rw [nn, map_div₀, map_neg, map_mul, map_add, conj_conj, mul_comm, add_comm]

theorem nn_ne_zero {b : K} (hb : b ≠ 0) (htr : b + J.conj b ≠ 0) : nn J b ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hb ((map_ne_zero J.conj).2 hb))) htr

variable {J} [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem neg_one_ne_one : (-1 : K) ≠ 1 := by
  intro e
  exact H.two_ne_zero' (by linear_combination -e)

omit [Finite K] in
theorem neg_one_pow : (-1 : K) ^ (q + 1) = 1 := by
  obtain ⟨m, hm⟩ := H.q_odd
  rw [hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul, neg_one_sq, one_pow]

omit [Finite K] H in
theorem exists_coord_two : ∃ z : Coord J, z.1.2 = -2 ∧ z.1.1 = 2 := by
  refine ⟨⟨(2, -2), ?_⟩, rfl, rfl⟩
  change (-2 : K) + J.conj (-2) + 2 * J.conj 2 = 0
  have h2 : J.conj (2 : K) = 2 := by
    rw [show (2 : K) = 1 + 1 by norm_num, map_add, map_one]
  rw [map_neg, h2]; ring

theorem eps_inv (k : Kˣ) : eps J σ k⁻¹ = eps J σ k := by
  have h1 := eps_mul (J := J) (σ := σ) k k⁻¹
  rw [mul_inv_cancel, show eps J σ 1 = 1 by simp [eps]] at h1
  have h2 := H.eps_mul_self k
  have he0 : eps J σ k ≠ 0 := by intro e; rw [e, zero_mul] at h2; exact zero_ne_one h2
  exact mul_left_cancel₀ he0 (h1.symm.trans h2.symm)

omit [Finite K] in
theorem inv_mul_torus_val {k : Kˣ} (hk : (k : K) ^ (q + 1) = 1) (u : Coord J) :
    (u⁻¹ * hermitianTorusAction J k u).1.1 = ((k : K) ^ 3 - 1) * u.1.1 ∧
      (u⁻¹ * hermitianTorusAction J k u).1.2 =
        (J.conj ((k : K) ^ 3) - 1) * (u.1.1 * J.conj u.1.1) := by
  rw [H.torus_nrm_one hk u]
  constructor
  · change -u.1.1 + u.1.1 * (k : K) ^ 3 = _
    ring
  · change J.conj u.1.2 + u.1.2 - -u.1.1 * J.conj (u.1.1 * (k : K) ^ 3) = _
    have := coord_rel u
    rw [map_mul]
    linear_combination this

theorem exists_coord_fst {a : K} : ∃ u : Coord J, u.1.1 = a := by
  have h2 := H.two_ne_zero'
  refine ⟨⟨(a, -(a * J.conj a) / 2), ?_⟩, rfl⟩
  change -(a * J.conj a) / 2 + J.conj (-(a * J.conj a) / 2) + a * J.conj a = 0
  have hc2 : J.conj (2 : K) = 2 := by
    rw [show (2 : K) = 1 + 1 by norm_num, map_add, map_one]
  rw [map_div₀, map_neg, map_mul, conj_conj, hc2]
  field_simp
  ring

theorem gam_block {n : K} (hn : n ≠ 0) (hnc : J.conj n = n) {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ : ζ ^ (q + 1) = 1) (hζ1 : ζ ≠ 1) :
    gam J F ((J.conj ζ - 1) * n) * (ζ - 1) = -2 * gam J F (-2 * n) := by
  obtain ⟨a, ha⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hn hnc
  obtain ⟨u, hu⟩ := H.exists_coord_fst (a := (a : K))
  have hua : u.1.1 ≠ 0 := by rw [hu]; exact a.ne_zero
  have hN : u.1.1 * J.conj u.1.1 = n := by rw [hu]; exact ha
  obtain ⟨k, hk, hk3⟩ := H.exists_cube_root hζ0 hζ
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hζ1 (by rw [← hk3]; simp)
  obtain ⟨k', hk', hk'3⟩ := H.exists_cube_root (neg_ne_zero.mpr one_ne_zero) H.neg_one_pow
  have hk'1 : k' ≠ 1 := by
    rintro rfl
    exact H.neg_one_ne_one (by rw [← hk'3]; simp)
  have hB := H.F_block u hua k k' hk hk' hk1 hk'1
  obtain ⟨e1, e2⟩ := H.inv_mul_torus_val hk u
  obtain ⟨e1', e2'⟩ := H.inv_mul_torus_val hk' u
  have hv : (u⁻¹ * hermitianTorusAction J k u).1.1 ≠ 0 := by
    rw [e1, hk3]; exact mul_ne_zero (sub_ne_zero.mpr hζ1) hua
  have hv' : (u⁻¹ * hermitianTorusAction J k' u).1.1 ≠ 0 := by
    rw [e1', hk'3]
    exact mul_ne_zero (by intro e; exact H.two_ne_zero' (by linear_combination -e)) hua
  rw [H.F_fst_eq hv, H.F_fst_eq hv', e1, e2, e1', e2', hk3, hk'3, hN] at hB
  have hc1 : J.conj (-1 : K) = -1 := by rw [map_neg, map_one]
  rw [hc1] at hB
  have hB' : gam J F ((J.conj ζ - 1) * n) * (ζ - 1) * u.1.1 =
      -2 * gam J F (-2 * n) * u.1.1 := by
    rw [show (-1 - 1 : K) * n = -2 * n by ring] at hB
    linear_combination hB
  exact mul_right_cancel₀ hua hB'

theorem gam_eq : ∃ c₀ : K, c₀ ≠ 0 ∧ ∀ b : K, b + J.conj b ≠ 0 →
    gam J F b = c₀ * sgn J σ (nn J b) / J.conj b := by
  obtain ⟨z₂, hz₂b, hz₂a⟩ := exists_coord_two (J := J)
  have hz₂ : z₂.1.1 ≠ 0 := by rw [hz₂a]; exact H.two_ne_zero'
  have hg2 : gam J F (-2) ≠ 0 := by have := H.gam_ne_zero hz₂; rwa [hz₂b] at this
  refine ⟨-2 * gam J F (-2), mul_ne_zero (neg_ne_zero.mpr H.two_ne_zero') hg2, ?_⟩
  intro b hb
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hcb0 : J.conj b ≠ 0 := (map_ne_zero J.conj).2 hb0
  set n := nn J b with hndef
  have hn : n ≠ 0 := nn_ne_zero J hb0 hb
  have hnc : J.conj n = n := conj_nn J b
  set ζ := 1 + J.conj b / n with hζdef
  have hnb : n * (b + J.conj b) = -(b * J.conj b) := by
    rw [hndef, nn]; field_simp
  have hcζ : J.conj ζ = 1 + b / n := by
    rw [hζdef, map_add, map_one, map_div₀, conj_conj, hnc]
  have hζn : ζ * J.conj ζ = 1 := by
    rw [hcζ, hζdef]
    field_simp
    linear_combination hnb
  have hζ0 : ζ ≠ 0 := by
    intro e; rw [e, zero_mul] at hζn; exact zero_ne_one hζn
  have hζ : ζ ^ (q + 1) = 1 := by rw [← H.nrm_eq_pow', nrm_def]; exact hζn
  have hζ1 : ζ ≠ 1 := by
    intro e
    rw [hζdef, add_eq_left] at e
    exact div_ne_zero hcb0 hn e
  have hblock := H.gam_block hn hnc hζ0 hζ hζ1
  rw [hcζ, show (1 + b / n - 1) * n = b by field_simp; ring,
    show ζ - 1 = J.conj b / n by rw [hζdef]; ring] at hblock
  have hni : n⁻¹ ≠ 0 := inv_ne_zero hn
  have hnic : J.conj n⁻¹ = n⁻¹ := by rw [map_inv₀, hnc]
  obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hni hnic
  have hT := (H.gam_emm_torus hz₂ k).1
  have hk' : (k : K) * J.conj (k : K) = n⁻¹ := hk
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have harg : z₂.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹ = -2 * n := by
    rw [hz₂b, mul_assoc, ← mul_inv, mul_comm (J.conj _), hk', inv_inv]
  rw [harg, hz₂b, hk] at hT
  have hsgn : sgn J σ n = eps J σ k := by
    have := H.sgn_nrm k⁻¹
    rw [Units.val_inv_eq_inv_val, nrm_inv, hk, inv_inv, H.eps_inv] at this
    exact this
  rw [hT] at hblock
  rw [hsgn]
  field_simp at hblock ⊢
  linear_combination hblock

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
