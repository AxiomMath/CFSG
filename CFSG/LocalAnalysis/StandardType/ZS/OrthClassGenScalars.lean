module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime]

private theorem ocg_two_ne_zero (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h))

private theorem ocg_three_ne_zero (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
    ((ZMod.natCast_eq_zero_iff 3 p).mp h))

private theorem ocg_sq_sub_ne_zero {κ : ZMod p} {m : ℕ}
    (hm8 : (m : ZMod p) ^ 8 ≠ κ ^ 4) : (m : ZMod p) ^ 2 - κ ≠ 0 := by
  intro h
  apply hm8
  have hκ : κ = (m : ZMod p) ^ 2 := by
    rw [eq_comm]
    exact sub_eq_zero.mp h
  rw [hκ]
  ring

private theorem ocg_sq_add_ne_zero {κ : ZMod p} {m : ℕ}
    (hm8 : (m : ZMod p) ^ 8 ≠ κ ^ 4) : (m : ZMod p) ^ 2 + κ ≠ 0 := by
  intro h
  apply hm8
  have hκ : κ = -((m : ZMod p) ^ 2) := by
    have h' : (m : ZMod p) ^ 2 + κ = 0 := h
    linear_combination h'
  rw [hκ]
  ring

private theorem ocg_four_add_ne_zero {κ : ZMod p} {m : ℕ}
    (hm8 : (m : ZMod p) ^ 8 ≠ κ ^ 4) : (m : ZMod p) ^ 4 + κ ^ 2 ≠ 0 := by
  intro h
  apply hm8
  have hκ : κ ^ 2 = -((m : ZMod p) ^ 4) := by linear_combination h
  calc (m : ZMod p) ^ 8 = (-((m : ZMod p) ^ 4)) ^ 2 := by ring
    _ = (κ ^ 2) ^ 2 := by rw [← hκ]
    _ = κ ^ 4 := by ring

private theorem ocg_exists_m_ne_pow (hp5 : p ≠ 5) {κ : ZMod p} :
    ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) ∧ (m : ZMod p) ^ 8 ≠ κ ^ 4 := by
  by_contra h
  push Not at h
  have h1 := h 1 (Or.inl rfl)
  have h2 := h 2 (Or.inr (Or.inl rfl))
  have h3 := h 3 (Or.inr (Or.inr rfl))
  have hp1 : (1 : ZMod p) = κ ^ 4 := by simpa using h1
  have hp2 : (256 : ZMod p) = κ ^ 4 := by
    have h2' : ((2 : ℕ) : ZMod p) ^ 8 = (256 : ZMod p) := by norm_num
    rw [h2'] at h2
    exact h2
  have hp3' : (6561 : ZMod p) = κ ^ 4 := by
    have h3' : ((3 : ℕ) : ZMod p) ^ 8 = (6561 : ZMod p) := by norm_num
    rw [h3'] at h3
    exact h3
  have h255 : (255 : ZMod p) = 0 := by
    have h256 : (256 : ZMod p) = (1 : ZMod p) := by rw [hp2, hp1]
    have h' : (256 : ZMod p) - 1 = 0 := by rw [h256]; ring
    norm_num at h'
    exact h'
  have h6560 : (6560 : ZMod p) = 0 := by
    have h6561 : (6561 : ZMod p) = (1 : ZMod p) := by rw [hp3', hp1]
    have h' : (6561 : ZMod p) - 1 = 0 := by rw [h6561]; ring
    norm_num at h'
    exact h'
  have hdvd5 : p ∣ 5 := by
    have hd := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff 255 p).mp h255)
      ((ZMod.natCast_eq_zero_iff 6560 p).mp h6560)
    norm_num at hd
    exact hd
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).mp hdvd5)

private theorem ocg_conic_off_axes (hp : p ≠ 2) {k : ZMod p} {m : ℕ}
    (hm0 : (m : ZMod p) ≠ 0) (hsub : 1 - k * (m : ZMod p) ^ 2 ≠ 0)
    (hadd : 1 + k * (m : ZMod p) ^ 2 ≠ 0) :
    ∃ s t : ZMod p, s ≠ 0 ∧ t ≠ 0 ∧ s ^ 2 + k * t ^ 2 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ocg_two_ne_zero hp
  refine ⟨(1 - k * (m : ZMod p) ^ 2) / (1 + k * (m : ZMod p) ^ 2),
    (2 * (m : ZMod p)) / (1 + k * (m : ZMod p) ^ 2), ?_, ?_, ?_⟩
  · exact div_ne_zero hsub hadd
  · exact div_ne_zero (mul_ne_zero h2 hm0) hadd
  · field_simp
    ring

private theorem ocg_conic_snd (hp : p ≠ 2) {k : ZMod p} {m : ℕ}
    (hm0 : (m : ZMod p) ≠ 0) (hadd : 1 + k * (m : ZMod p) ^ 2 ≠ 0) :
    ∃ s t : ZMod p, t ≠ 0 ∧ s ^ 2 + k * t ^ 2 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ocg_two_ne_zero hp
  refine ⟨(1 - k * (m : ZMod p) ^ 2) / (1 + k * (m : ZMod p) ^ 2),
    (2 * (m : ZMod p)) / (1 + k * (m : ZMod p) ^ 2), ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero h2 hm0) hadd
  · field_simp
    ring

private theorem ocg_four_eq_pm_one {k : ZMod p}
    (hk1 : k = 1 ∨ k = -1) (hk4 : (4 : ZMod p) * k = 1 ∨ (4 : ZMod p) * k = -1) :
    (4 : ZMod p) = 1 ∨ (4 : ZMod p) = -1 := by
  rcases hk1 with hk1 | hk1
  · rw [hk1] at hk4; simpa using hk4
  · rw [hk1] at hk4
    rcases hk4 with hk4 | hk4
    · right; linear_combination -hk4
    · left; linear_combination -hk4

private theorem ocg_false_of_conic_fail (hp3 : p ≠ 3) {k : ZMod p}
    (h5 : p = 5 → ¬ IsSquare k) (hk1 : k = 1 ∨ k = -1)
    (hk4 : (4 : ZMod p) * k = 1 ∨ (4 : ZMod p) * k = -1) : False := by
  have h4 : (4 : ZMod p) = 1 ∨ (4 : ZMod p) = -1 := ocg_four_eq_pm_one hk1 hk4
  have hp5eq : p = 5 := by
    rcases h4 with h4 | h4
    · exfalso
      have h3 : (3 : ZMod p) = 0 := by
        have h' : (4 : ZMod p) - 1 = 0 := by rw [h4]; ring
        norm_num at h'
        exact h'
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
        ((ZMod.natCast_eq_zero_iff 3 p).mp h3))
    · have h5z : (5 : ZMod p) = 0 := by
        have h' : (4 : ZMod p) + 1 = 0 := by rw [h4]; ring
        norm_num at h'
        exact h'
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).mp
        ((ZMod.natCast_eq_zero_iff 5 p).mp h5z)
  have hksq : IsSquare k := by
    rcases hk1 with hk1 | hk1
    · rw [hk1]; exact IsSquare.one
    · rw [hk1]
      rcases h4 with h4 | h4
      · exfalso
        have h3 : (3 : ZMod p) = 0 := by
          have h' : (4 : ZMod p) - 1 = 0 := by rw [h4]; ring
          norm_num at h'
          exact h'
        exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
          ((ZMod.natCast_eq_zero_iff 3 p).mp h3))
      · exact ⟨2, by rw [← h4]; norm_num⟩
  exact h5 hp5eq hksq

private theorem ocg_exists_m_conic (hp3 : p ≠ 3) {k : ZMod p} (h5 : p = 5 → ¬ IsSquare k) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ 1 - k * (m : ZMod p) ^ 2 ≠ 0 ∧
      1 + k * (m : ZMod p) ^ 2 ≠ 0 := by
  by_contra h
  push Not at h
  have hm1 := h 1 (Or.inl rfl)
  have hm2 := h 2 (Or.inr rfl)
  have hk1 : k = 1 ∨ k = -1 := by
    by_cases h0 : 1 - k * ((1 : ℕ) : ZMod p) ^ 2 = 0
    · left
      have h' : k * ((1 : ℕ) : ZMod p) ^ 2 = 1 := (sub_eq_zero.mp h0).symm
      simpa using h'
    · right
      have hb := hm1 h0
      rw [add_comm] at hb
      have h' : k * ((1 : ℕ) : ZMod p) ^ 2 = -1 := add_eq_zero_iff_eq_neg.mp hb
      simpa using h'
  have hk4 : (4 : ZMod p) * k = 1 ∨ (4 : ZMod p) * k = -1 := by
    by_cases h0 : 1 - k * ((2 : ℕ) : ZMod p) ^ 2 = 0
    · left
      have h4 : k * ((2 : ℕ) : ZMod p) ^ 2 = 1 := (sub_eq_zero.mp h0).symm
      norm_num at h4
      rwa [mul_comm] at h4
    · right
      have hb := hm2 h0
      have h4 : k * ((2 : ℕ) : ZMod p) ^ 2 = -1 := by
        rw [add_comm] at hb
        exact add_eq_zero_iff_eq_neg.mp hb
      norm_num at h4
      rwa [mul_comm] at h4
  exact ocg_false_of_conic_fail hp3 h5 hk1 hk4

private theorem ocg_exists_m_conic_snd (hp3 : p ≠ 3) {k : ZMod p} :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ 1 + k * (m : ZMod p) ^ 2 ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := h 1 (Or.inl rfl)
  have h2 := h 2 (Or.inr rfl)
  have hk1 : k = -1 := by linear_combination h1
  have h3 : (3 : ZMod p) = 0 := by
    rw [hk1] at h2
    linear_combination -h2
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
    ((ZMod.natCast_eq_zero_iff 3 p).mp h3))


theorem exists_threeMinus_scalars (hp : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) {κ : ZMod p}
    (hκ : κ ≠ 0) :
    ∃ lam t : ZMod p, lam ≠ 0 ∧ lam ^ 4 ≠ 1 ∧ t ≠ 0 ∧ κ * (1 - lam ^ 2) = t ^ 2 := by
  obtain ⟨m, hm123, hm8⟩ := ocg_exists_m_ne_pow hp5
  have hm0 : (m : ZMod p) ≠ 0 := by
    rcases hm123 with h | h | h
    · rw [h, Nat.cast_one]; exact one_ne_zero
    · rw [h]; simpa using ocg_two_ne_zero hp
    · rw [h]; simpa using ocg_three_ne_zero hp3
  have h2 : (2 : ZMod p) ≠ 0 := ocg_two_ne_zero hp
  have h8 : (8 : ZMod p) ≠ 0 := by
    have : (8 : ZMod p) = (2 : ZMod p) ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h2
  have hsub : (m : ZMod p) ^ 2 - κ ≠ 0 := ocg_sq_sub_ne_zero hm8
  have hadd : (m : ZMod p) ^ 2 + κ ≠ 0 := ocg_sq_add_ne_zero hm8
  have hfour : (m : ZMod p) ^ 4 + κ ^ 2 ≠ 0 := ocg_four_add_ne_zero hm8
  have hm0sq : (m : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  set lam : ZMod p := ((m : ZMod p) ^ 2 - κ) / ((m : ZMod p) ^ 2 + κ) with hlam
  set t : ZMod p := -(2 * κ * (m : ZMod p)) / ((m : ZMod p) ^ 2 + κ) with ht
  refine ⟨lam, t, ?_, ?_, ?_, ?_⟩
  · rw [hlam]; exact div_ne_zero hsub hadd
  · intro h1
    have hne : lam ^ 4 - 1 ≠ 0 := by
      have hcompute : lam ^ 4 - 1 =
          -(8 * (m : ZMod p) ^ 2 * κ * ((m : ZMod p) ^ 4 + κ ^ 2)) /
            ((m : ZMod p) ^ 2 + κ) ^ 4 := by
        rw [hlam]; field_simp; ring
      rw [hcompute]
      exact div_ne_zero
        (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero h8 hm0sq) hκ) hfour))
        (pow_ne_zero 4 hadd)
    exact hne (by rw [h1]; ring)
  · rw [ht]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h2 hκ) hm0)) hadd
  · rw [hlam, ht]
    field_simp
    ring

theorem exists_conic_point_ne_zero (hp : p ≠ 2) (hp3 : p ≠ 3) {k : ZMod p} (_hk : k ≠ 0)
    (h5 : p = 5 → ¬ IsSquare k) : ∃ s t : ZMod p, s ≠ 0 ∧ t ≠ 0 ∧ s ^ 2 + k * t ^ 2 = 1 := by
  obtain ⟨m, hm12, hsub, hadd⟩ := ocg_exists_m_conic hp3 h5
  have hm0 : (m : ZMod p) ≠ 0 := by
    rcases hm12 with h | h
    · rw [h, Nat.cast_one]; exact one_ne_zero
    · rw [h]; simpa using ocg_two_ne_zero hp
  exact ocg_conic_off_axes hp hm0 hsub hadd

theorem exists_conic_point_snd_ne_zero (hp3 : p ≠ 3) {k : ZMod p} (hk : k ≠ 0) :
    ∃ s t : ZMod p, t ≠ 0 ∧ s ^ 2 + k * t ^ 2 = 1 := by
  by_cases hp2 : p = 2
  · have hk1 : k = 1 := by
      have hlt : k.val < 2 := by
        have h := @ZMod.val_lt p ⟨(Fact.out : p.Prime).ne_zero⟩ k
        exact lt_of_lt_of_eq h hp2
      have hle : k.val ≤ 1 := Nat.lt_succ_iff.mp hlt
      have hval : k.val = 0 ∨ k.val = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hle
      have hcast : ((k.val : ℕ) : ZMod p) = k :=
        @ZMod.natCast_zmod_val p ⟨(Fact.out : p.Prime).ne_zero⟩ k
      rcases hval with h | h
      · exact absurd (by rw [← hcast, h]; norm_num : k = 0) hk
      · rw [← hcast, h]; norm_num
    refine ⟨0, (1 : ZMod p), ?_, ?_⟩
    · exact one_ne_zero
    · rw [hk1]; norm_num
  · obtain ⟨m, hm12, hadd⟩ := ocg_exists_m_conic_snd hp3
    have hm0 : (m : ZMod p) ≠ 0 := by
      rcases hm12 with h | h
      · rw [h, Nat.cast_one]; exact one_ne_zero
      · rw [h]; simpa using ocg_two_ne_zero hp2
    exact ocg_conic_snd hp2 hm0 hadd

end CFSG.StandardType.ZS
