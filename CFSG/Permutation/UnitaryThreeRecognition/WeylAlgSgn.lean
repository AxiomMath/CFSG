module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgPigeon

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem nn_div {κ b : K} (hκ : κ ≠ 0) (hκc : J.conj κ = κ) (hb0 : b ≠ 0)
    (hb : b + J.conj b ≠ 0) : nn J (κ / b) = κ * nn J b / (b * J.conj b) := by
  have hcb : J.conj b ≠ 0 := (map_ne_zero J.conj).2 hb0
  have e1 : nn J (κ / b) = -κ / (b + J.conj b) := by
    rw [nn, map_div₀, hκc]
    rw [show κ / b + κ / J.conj b = κ * (b + J.conj b) / (b * J.conj b) by field_simp; ring,
      show κ / b * (κ / J.conj b) = κ * κ / (b * J.conj b) by field_simp]
    rw [neg_div, neg_div, div_div_div_cancel_right₀ (mul_ne_zero hb0 hcb)]
    rw [mul_div_mul_left _ _ hκ]
  have e2 : κ * nn J b / (b * J.conj b) = -κ / (b + J.conj b) := by
    rw [nn, div_eq_div_iff (mul_ne_zero hb0 hcb) hb, mul_assoc, div_mul_cancel₀ _ hb]; ring
  rw [e1, e2]

variable [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem sgn_mul {x y : K} (hx : x ≠ 0) (hxc : J.conj x = x) (hy : y ≠ 0)
    (hyc : J.conj y = y) : sgn J σ (x * y) = sgn J σ x * sgn J σ y := by
  obtain ⟨k₁, rfl⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hx hxc
  obtain ⟨k₂, rfl⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hy hyc
  rw [← nrm_mul, ← Units.val_mul, H.sgn_nrm, H.sgn_nrm, H.sgn_nrm, eps_mul]

theorem sgn_inv' {x : K} (hx : x ≠ 0) (hxc : J.conj x = x) : sgn J σ x⁻¹ = sgn J σ x := by
  obtain ⟨k, rfl⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hx hxc
  rw [← nrm_inv, ← Units.val_inv_eq_inv_val, H.sgn_nrm, H.sgn_nrm, H.eps_inv]

theorem exists_nrm_tr {y : K} (hy : y ≠ 0) (hyc : J.conj y = y) :
    ∃ b : K, b + J.conj b ≠ 0 ∧ nrm J b = y := by
  obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hy hyc
  by_cases htr : (k : K) + J.conj k = 0
  ·
    have hck : J.conj (k : K) = -k := by linear_combination htr
    have hk0 : (k : K) ≠ 0 := k.ne_zero
    have h2 := H.two_ne_zero'
    have hk1 : (k : K) ^ 2 ≠ 1 := by
      intro e
      have hk2 : J.conj ((k : K) ^ 2) = (k : K) ^ 2 := by rw [map_pow, hck]; ring
      have e' : (k : K) * k = 1 := by rw [← sq]; exact e
      rcases mul_self_eq_one_iff.mp e' with e1 | e1
      · apply h2; have := congrArg J.conj e1; rw [hck, map_one] at this
        linear_combination -this - e1
      · apply h2; have := congrArg J.conj e1; rw [hck, map_neg, map_one] at this
        linear_combination this + e1
    have hp : (k : K) + 1 ≠ 0 := by
      intro e; apply hk1; rw [show (k : K) = -1 by linear_combination e]; ring
    have hm : 1 - (k : K) ≠ 0 := by
      intro e; apply hk1; rw [show (k : K) = 1 by linear_combination -e]; ring
    have hp1 : 1 + (k : K) ≠ 0 := by rw [add_comm]; exact hp
    have hp2 : 1 - -(k : K) ≠ 0 := by rw [sub_neg_eq_add]; exact hp1
    refine ⟨k * (k + 1) / (1 - k), ?_, ?_⟩
    · rw [map_div₀, map_mul, map_add, map_sub, map_one, hck]
      intro e
      have key : (k * (k + 1) / (1 - k) + -k * (-k + 1) / (1 - -k)) * ((1 - k) * (1 - -k)) =
          4 * (k : K) ^ 2 := by
        field_simp
        ring
      rw [e, zero_mul] at key
      have h4 : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
      exact pow_ne_zero 2 hk0 ((mul_eq_zero.mp key.symm).resolve_left h4)
    · rw [nrm_def, map_div₀, map_mul, map_add, map_sub, map_one, hck, ← hk, nrm_def, hck]
      field_simp
      ring
  · exact ⟨k, htr, hk⟩

theorem sgn_eq_one {κ : K} (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
      (F z).1.1 = 0 ∧ (F z).1.2 = κ / z.1.2)
    (hκ0 : κ ≠ 0) (hκc : J.conj κ = κ) {c₀ : K} (hc₀0 : c₀ ≠ 0)
    (hgam : ∀ b : K, b + J.conj b ≠ 0 → gam J F b = c₀ * sgn J σ (nn J b) / J.conj b)
    {c₁ : K} (hc₁0 : c₁ ≠ 0) (hc₁ : J.conj c₁ = -c₁) :
    (∀ y : K, y ≠ 0 → J.conj y = y → sgn J σ y = 1) ∧ c₀ ^ 2 = κ := by
  have key : ∀ b : K, b + J.conj b ≠ 0 →
      c₀ ^ 2 * sgn J σ κ * sgn J σ (b * J.conj b) = κ := by
    intro b hb
    obtain ⟨w, hwb, hwa⟩ := H.exists_coord hb
    have hw1 : w ≠ 1 := fun e => hwa (by rw [e]; rfl)
    have hFw := H.F_ne_center hwa
    have hFF := congrArg (fun v : Coord J => v.1.1) (H.F_F w hw1)
    change (F (F w)).1.1 = w.1.1 at hFF
    rw [H.F_fst_eq hFw, H.F_snd_eq hwa, H.F_fst_eq hwa,
      (H.emm_eq hκF hκ0 hκc hc₀0 hgam hc₁0 hc₁ hwa).1, hwb] at hFF
    have hb0 : b ≠ 0 := by intro e; apply hb; rw [e, map_zero, add_zero]
    have hcb0 : J.conj b ≠ 0 := (map_ne_zero J.conj).2 hb0
    have hκb : κ / b + J.conj (κ / b) ≠ 0 := by
      rw [map_div₀, hκc]
      intro e
      apply hb
      have : κ * (b + J.conj b) = 0 := by field_simp at e; linear_combination e
      exact (mul_eq_zero.mp this).resolve_left hκ0
    rw [hgam _ hκb, hgam _ hb, nn_div hκ0 hκc hb0 hb] at hFF
    have hN0 : b * J.conj b ≠ 0 := mul_ne_zero hb0 hcb0
    have hNc : J.conj (b * J.conj b) = b * J.conj b := by rw [map_mul, conj_conj, mul_comm]
    have hn0 : nn J b ≠ 0 := nn_ne_zero J hb0 hb
    have hnc : J.conj (nn J b) = nn J b := conj_nn J b
    have hκn0 : κ * nn J b ≠ 0 := mul_ne_zero hκ0 hn0
    have hκnc : J.conj (κ * nn J b) = κ * nn J b := by rw [map_mul, hκc, hnc]
    rw [div_eq_mul_inv (κ * nn J b), H.sgn_mul hκn0 hκnc (inv_ne_zero hN0)
      (by rw [map_inv₀, hNc]), H.sgn_inv' hN0 hNc, H.sgn_mul hκ0 hκc hn0 hnc] at hFF
    have hs := H.sgn_mul_self (nn J b)
    rw [map_div₀, hκc] at hFF
    have ha : w.1.1 ≠ 0 := hwa
    field_simp at hFF
    linear_combination hFF - (c₀ ^ 2 * sgn J σ κ * sgn J σ (b * J.conj b)) * hs
  have h1 : sgn J σ 1 = 1 := by
    have := H.sgn_nrm 1
    rw [Units.val_one, nrm_def, map_one, mul_one] at this
    rw [this]; simp [eps]
  have hone : (1 : K) + J.conj 1 ≠ 0 := by
    rw [map_one]; have := H.two_ne_zero'; rwa [one_add_one_eq_two]
  have k1 := key 1 hone
  rw [map_one, mul_one, h1, mul_one] at k1
  have hall : ∀ y : K, y ≠ 0 → J.conj y = y → sgn J σ y = 1 := by
    intro y hy hyc
    obtain ⟨b, hb, hby⟩ := H.exists_nrm_tr hy hyc
    have k2 := key b hb
    rw [← nrm_def, hby, k1] at k2
    have : κ * sgn J σ y = κ * 1 := by rw [mul_one]; exact k2
    exact mul_left_cancel₀ hκ0 this
  refine ⟨hall, ?_⟩
  rw [hall κ hκ0 hκc, mul_one] at k1
  exact k1

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
