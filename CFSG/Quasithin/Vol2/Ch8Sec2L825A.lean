module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Zify
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13

theorem two_mul_le_two_pow_82 {x : ℕ} (hx : 1 ≤ x) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num
    · have := ih hm
      rw [pow_succ]
      omega

theorem pow_sub_one_eq_mul_82 (d e : ℕ) (he : 2 ≤ e) :
    ∃ q : ℕ, 2 ^ (d * e) - 1 = (2 ^ d - 1) * q ∧ 1 + 2 ^ (d * (e - 1)) ≤ q := by
  induction e, he using Nat.le_induction with
  | base =>
    refine ⟨2 ^ d + 1, ?_, le_of_eq (by rw [show d * (2 - 1) = d by omega, add_comm])⟩
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have h2 : 2 ^ (d * 2) = 2 ^ d * 2 ^ d := by rw [mul_two, pow_add]
    rw [h2]
    zify [h1, Nat.one_le_two_pow (n := d * 2), Nat.mul_le_mul h1 h1]
    ring
  | succ e he ih =>
    obtain ⟨q, hq, hq1⟩ := ih
    refine ⟨q + 2 ^ (d * e), ?_, ?_⟩
    · have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have h2 : 2 ^ (d * (e + 1)) = 2 ^ (d * e) * 2 ^ d := by rw [mul_add, mul_one, pow_add]
      have h3 : 1 ≤ 2 ^ (d * e) := Nat.one_le_two_pow
      rw [h2]
      have h4 : 1 ≤ 2 ^ (d * e) * 2 ^ d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      zify [h1, h3, h4] at hq ⊢
      rw [mul_add, ← hq]
      ring
    · have h5 : d * (e + 1 - 1) = d * e := by rw [Nat.add_sub_cancel]
      have h6 : 1 ≤ q := le_trans (Nat.le_add_right 1 _) hq1
      rw [h5]
      omega

theorem dvd_of_pow_sub_one_dvd_82 {k n : ℕ} (hn : 1 ≤ n) (hnk : n < k)
    (h : 2 ^ k - 1 ∣ (2 ^ (4 * n) - 1) * n) : k ∣ 4 * n := by
  set d := Nat.gcd k (4 * n) with hd
  have hdk : d ∣ k := Nat.gcd_dvd_left k (4 * n)
  have hdn : d ∣ 4 * n := Nat.gcd_dvd_right k (4 * n)
  by_contra hkn
  have hdlt : d ≠ k := fun h' => hkn (h' ▸ hdn)
  obtain ⟨e, he⟩ := hdk
  have hk0 : 0 < k := by omega
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at he; omega
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h' | h'
    · interval_cases e
      · rw [mul_zero] at he
        omega
      · rw [mul_one] at he
        exact absurd he.symm hdlt
    · exact h'
  obtain ⟨q, hq, hq1⟩ := pow_sub_one_eq_mul_82 d e he2
  rw [← he] at hq
  obtain ⟨f, hf⟩ := hdn
  obtain ⟨r, hr⟩ : 2 ^ d - 1 ∣ 2 ^ (4 * n) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 f
    rwa [one_pow, ← pow_mul, ← hf] at this
  have hg : Nat.gcd (2 ^ k - 1) (2 ^ (4 * n) - 1) = 2 ^ d - 1 :=
    Nat.pow_sub_one_gcd_pow_sub_one 2 k (4 * n)
  rw [hq, hr, Nat.gcd_mul_left] at hg
  have hg1 : 1 ≤ 2 ^ d - 1 := by
    have : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd0
    omega
  have hcop : Nat.gcd q r = 1 := by
    have h1 : (2 ^ d - 1) * Nat.gcd q r = (2 ^ d - 1) * 1 := by rw [hg, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  rw [hq, hr, mul_assoc] at h
  have h2 : q ∣ r * n := (Nat.mul_dvd_mul_iff_left (by omega)).mp h
  have h3 : q ∣ n := (Nat.Coprime.dvd_of_dvd_mul_left hcop h2)
  have h4 : q ≤ n := Nat.le_of_dvd (by omega) h3
  have h5 : 2 * (d * (e - 1)) ≤ 2 ^ (d * (e - 1)) :=
    two_mul_le_two_pow_82 (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
  have h6 : d * e ≤ 2 * (d * (e - 1)) := by
    have : e ≤ 2 * (e - 1) := by omega
    calc d * e ≤ d * (2 * (e - 1)) := Nat.mul_le_mul_left d this
      _ = 2 * (d * (e - 1)) := by ring
  omega

theorem eq_two_mul_or_of_dvd_82 {k n : ℕ} (hnk : n < k) (hk : k ≤ 2 * n) (h : k ∣ 4 * n) :
    k = 2 * n ∨ 3 * k = 4 * n := by
  obtain ⟨j, hj⟩ := h
  have hj4 : j < 4 := by
    by_contra hj4
    push Not at hj4
    have : k * 4 ≤ k * j := Nat.mul_le_mul_left k hj4
    omega
  have hj2 : 2 ≤ j := by
    by_contra hj2
    push Not at hj2
    interval_cases j <;> omega
  interval_cases j
  · left
    omega
  · right
    omega

end CFSG.Quasithin.H13
