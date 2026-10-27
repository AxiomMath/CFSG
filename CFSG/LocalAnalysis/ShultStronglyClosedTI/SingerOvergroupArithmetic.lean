module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ShultStronglyClosedTI.Singer

theorem two_mul_le_two_pow (x : ℕ) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h2 : 2 ≤ 2 ^ n :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega

theorem three_mul_lt_two_pow {s : ℕ} (hs : 4 ≤ s) : 3 * s < 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

theorem sum_range_succ_pow (b n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), b ^ i = b * ∑ i ∈ Finset.range n, b ^ i + 1 := by
  rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [pow_succ, mul_comm]

theorem not_sum_pow_dvd {s m : ℕ} (hs : 1 ≤ s) (hm : 3 ≤ m) (heven : Even (s * m)) :
    ¬ (∑ i ∈ Finset.range (m - 1), (2 ^ s) ^ i) ∣ s * m := by
  intro hdvd
  have hpos : 0 < s * m := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  ·
    have hm3 : m = 3 := by omega
    subst hm3
    have hT : ∑ i ∈ Finset.range (3 - 1), (2 ^ s) ^ i = 1 + 2 ^ s := by
      simp [Finset.sum_range_succ]
    rw [hT] at hdvd hle
    have hseven : Even s := by
      rcases Nat.even_mul.mp heven with h | h
      · exact h
      · exact absurd h (by decide)
    rcases Nat.lt_or_ge s 4 with hs4 | hs4
    · obtain ⟨j, hj⟩ := hseven
      have hs2 : s = 2 := by omega
      subst hs2
      norm_num at hdvd
    · have := three_mul_lt_two_pow hs4
      omega
  ·
    have h02 : ({0, m - 2} : Finset ℕ) ⊆ Finset.range (m - 1) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      omega
    have hge : 1 + (2 ^ s) ^ (m - 2) ≤ ∑ i ∈ Finset.range (m - 1), (2 ^ s) ^ i := by
      have := Finset.sum_le_sum_of_subset (f := fun i => (2 ^ s) ^ i) h02
      rw [Finset.sum_pair (by omega)] at this
      simpa using this
    have hpow : (2 ^ s) ^ (m - 2) = 2 ^ (s * (m - 2)) := by rw [← pow_mul]
    have hlin := two_mul_le_two_pow (s * (m - 2))
    have hsm : s * m = s * (m - 2) + s * 2 := by rw [← Nat.mul_add]; congr 1; omega
    have h4 : s * 2 ≤ s * (m - 2) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem not_sum_pow_sub_one_dvd {s m d : ℕ} (hs : 1 ≤ s) (hm : 3 ≤ m) (heven : Even (s * m))
    (hde : d ∣ s * m) :
    ¬ (∑ i ∈ Finset.range m, (2 ^ s) ^ i) - 1 ∣ 2 ^ (s * m) * d := by
  intro hdvd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
  rw [show 2 + n = (n + 1) + 1 by ring, sum_range_succ_pow, Nat.add_sub_cancel] at hdvd
  have hm1 : 2 + n - 1 = n + 1 := by omega
  have hTodd : Odd (∑ i ∈ Finset.range (n + 1), (2 ^ s) ^ i) := by
    rw [sum_range_succ_pow]
    have h2 : Even (2 ^ s) := (Nat.even_pow' (by omega)).mpr even_two
    exact Even.add_one (h2.mul_right _)
  have hTd : (∑ i ∈ Finset.range (n + 1), (2 ^ s) ^ i) ∣ d := by
    have h1 := (Dvd.intro_left _ rfl).trans hdvd
    have hcop : Nat.Coprime (∑ i ∈ Finset.range (n + 1), (2 ^ s) ^ i) (2 ^ (s * (n + 1 + 1))) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hTodd)
    exact hcop.dvd_of_dvd_mul_left h1
  have := not_sum_pow_dvd hs hm heven
  rw [hm1] at this
  exact this (hTd.trans hde)

theorem not_two_pow_dvd_of_dvd_card_GL_two {s a N : ℕ} (hs : 1 ≤ s) (ha : 1 ≤ a) (has : a ≤ s)
    (hN : N ∣ ((2 ^ s) ^ 2 - 1) * ((2 ^ s) ^ 2 - 2 ^ s)) (h2 : 2 ^ (2 * s) ∣ N * a) : False := by
  have hb : 2 ≤ 2 ^ s :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have heb : Even (2 ^ s) := (Nat.even_pow' (by omega)).mpr even_two
  have hodd1 : Odd ((2 ^ s) ^ 2 - 1) := by
    have : Even ((2 ^ s) ^ 2) := (Nat.even_pow' (by norm_num)).mpr heb
    exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity)) this odd_one
  have hodd2 : Odd (2 ^ s - 1) := Nat.Even.sub_odd (by omega) heb odd_one
  have hfac : ((2 ^ s) ^ 2 - 2 ^ s) = 2 ^ s * (2 ^ s - 1) := by
    rw [sq, Nat.mul_sub, mul_one]
  have hdvd : 2 ^ s * 2 ^ s ∣ 2 ^ s * (((2 ^ s) ^ 2 - 1) * (2 ^ s - 1) * a) := by
    have := h2.trans (Nat.mul_dvd_mul_right hN a)
    rw [hfac, two_mul, pow_add] at this
    convert this using 1
    ring
  have hdvd' := Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd
  have hcop : Nat.Coprime (2 ^ s) (((2 ^ s) ^ 2 - 1) * (2 ^ s - 1)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (hodd1.mul hodd2))
  have hda : 2 ^ s ∣ a := hcop.dvd_of_dvd_mul_left hdvd'
  have := Nat.le_of_dvd (by omega) hda
  have := Nat.lt_two_pow_self (n := s)
  omega

theorem lt_of_card_eq {s m a d N e : ℕ} (he : e = s * m) (he1 : 1 ≤ e) (hd : 1 ≤ d)
    (has : a ≤ s) (hN : N * a = 2 ^ e * (2 ^ e - 1) * d) (hle : N ≤ (2 ^ e - 1) * m) : False := by
  have hq : 1 ≤ 2 ^ e - 1 := by
    have := Nat.one_lt_two_pow (show e ≠ 0 by omega)
    omega
  have h1 : 2 ^ e * (2 ^ e - 1) ≤ 2 ^ e * (2 ^ e - 1) * d := Nat.le_mul_of_pos_right _ hd
  have h2 : N * a ≤ (2 ^ e - 1) * m * s := Nat.mul_le_mul hle has
  have h3 : (2 ^ e - 1) * m * s = e * (2 ^ e - 1) := by rw [he]; ring
  have h4 : 2 ^ e * (2 ^ e - 1) ≤ e * (2 ^ e - 1) := by omega
  have h5 : 2 ^ e ≤ e := Nat.le_of_mul_le_mul_right h4 (by omega)
  have := Nat.lt_two_pow_self (n := e)
  omega

end CFSG.ShultStronglyClosedTI.Singer
