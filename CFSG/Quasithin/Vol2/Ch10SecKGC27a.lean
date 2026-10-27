module

public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

@[expose] def C27Order (N : ℕ) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ N = 2 ^ n * (4 ^ n - 1)) ∨ N = 60 ∨ N = 360 ∨ N = 2520 ∨ N = 20160 ∨
    N = 1080 ∨ N = 979200 ∨ N = 6048 ∨
    (∃ n : ℕ, 1 ≤ n ∧ N = 2 ^ (3 * n) * ((4 ^ n - 1) * (8 ^ n - 1))) ∨ N = 9999360

theorem not_sixteen_dvd {p : ℕ} (hp : p % 8 = 3 ∨ p % 8 = 5) : ¬ 16 ∣ p * (p ^ 2 - 1) := by
  intro h
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hz := (ZMod.natCast_eq_zero_iff (p * (p ^ 2 - 1)) 16).mpr h
  rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, ← ZMod.natCast_mod p 16] at hz
  have hr : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
  rcases hr with hr | hr | hr | hr <;> rw [hr] at hz <;> revert hz <;> decide

theorem eight_dvd_of_c27Order {N : ℕ} (h : C27Order N) (h60 : N ≠ 60) : 8 ∣ N := by
  rcases h with ⟨n, hn, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨n, hn, rfl⟩ | rfl
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact absurd rfl h60
    · exact Dvd.dvd.mul_right ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 hn3) _
  · exact absurd rfl h60
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact Dvd.dvd.mul_right ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 (by omega)) _
  · norm_num

theorem not_c27Order_psl_p {p N : ℕ} (hp : p.Prime) (h5 : p ^ 2 % 5 = 1)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (hN : 2 * N = p * (p ^ 2 - 1)) : ¬ C27Order N := by
  intro h
  by_cases h60 : N = 60
  · subst h60
    have hp6 : p ≤ 5 := by
      by_contra hp6
      have h36 : 36 ≤ p ^ 2 := by nlinarith
      have : 6 * 35 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases p <;> revert h5 hN <;> decide
  · obtain ⟨m, hm⟩ := eight_dvd_of_c27Order h h60
    exact not_sixteen_dvd h8 ⟨m, by rw [← hN, hm]; ring⟩

theorem sq_sub_one' (x : ℕ) : x ^ 2 - 1 = (x - 1) * (x + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

theorem two_pow_dvd_sq_sub_one {p k : ℕ} (hp : Odd p) (h : 2 ^ (k + 1) ∣ p ^ 2 * (p ^ 4 - 1)) :
    2 ^ k ∣ p ^ 2 - 1 := by
  obtain ⟨t, rfl⟩ := hp
  have h4 : (2 * t + 1) ^ 4 - 1 = ((2 * t + 1) ^ 2 - 1) * (2 * (2 * t ^ 2 + 2 * t + 1)) := by
    rw [show (2 * t + 1) ^ 4 = ((2 * t + 1) ^ 2) ^ 2 by ring, sq_sub_one']
    congr 1
    ring
  rw [h4, pow_succ',
    show (2 * t + 1) ^ 2 * (((2 * t + 1) ^ 2 - 1) * (2 * (2 * t ^ 2 + 2 * t + 1))) =
      2 * (((2 * t + 1) ^ 2 * (2 * t ^ 2 + 2 * t + 1)) * ((2 * t + 1) ^ 2 - 1)) by ring] at h
  have h' := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h
  refine (Nat.Coprime.dvd_of_dvd_mul_left ?_ h')
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_two_left]
  refine Odd.mul (Odd.pow ⟨t, rfl⟩) ⟨t ^ 2 + t, by ring⟩

theorem eq_four_of_eq {m : ℕ} (hm : 1 ≤ m)
    (h : (m + 1) * ((m + 1) ^ 2 - 1) = 2 * (m * (m ^ 2 - 1))) : m = 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e1 : (k + 1 + 1) ^ 2 - 1 = (k + 1) * (k + 3) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have e2 : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [e1, e2] at h
  have h' : ((k + 1) * (k + 2)) * (k + 3) = ((k + 1) * (k + 2)) * (2 * k) := by
    calc ((k + 1) * (k + 2)) * (k + 3) = (k + 1 + 1) * ((k + 1) * (k + 3)) := by ring
      _ = 2 * ((k + 1) * (k * (k + 2))) := h
      _ = ((k + 1) * (k + 2)) * (2 * k) := by ring
  have := Nat.eq_of_mul_eq_mul_left (by positivity) h'
  omega

theorem not_psl_p2_eq_sl2 {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hn : 2 ≤ n)
    (h : p ^ 2 * (p ^ 4 - 1) = 2 * (2 ^ n * (4 ^ n - 1))) : False := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hm4 : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hn
  have h4n : 4 ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4n] at h
  set m := 2 ^ n with hm
  have h16 : 16 ≤ p ^ 2 := by nlinarith
  have hdvd2 := two_pow_dvd_sq_sub_one hodd (k := n) ⟨m ^ 2 - 1, by rw [h, pow_succ, hm]; ring⟩
  have hge : m + 1 ≤ p ^ 2 := by
    have := Nat.le_of_dvd (by omega) hdvd2
    omega
  have hcop : Nat.Coprime (p ^ 2) (2 * m) := by
    rw [hm, ← pow_succ']
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have h1 : p ^ 2 ∣ (m - 1) * (m + 1) := by
    rw [← sq_sub_one']
    exact hcop.dvd_of_dvd_mul_left ⟨p ^ 4 - 1, by rw [h, mul_assoc]⟩
  have hcop' : Nat.Coprime (m - 1) (m + 1) := by
    rw [show m + 1 = m - 1 + 2 by omega, Nat.coprime_self_add_right, Nat.coprime_two_right]
    have he : Even m := hm ▸ (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact Nat.Even.sub_odd (by omega) he odd_one
  rcases (hcop'.isPrimePow_dvd_mul (hp.isPrimePow.pow (by norm_num))).mp h1 with h1' | h1'
  · have := Nat.le_of_dvd (by omega) h1'
    omega
  · have hx : p ^ 2 = m + 1 := le_antisymm (Nat.le_of_dvd (by omega) h1') hge
    rw [show p ^ 4 = (p ^ 2) ^ 2 by ring, hx] at h
    have h4 := eq_four_of_eq (by omega) h
    have h5 : p ^ 2 = 5 := by omega
    nlinarith

theorem not_psl_p2_eq_sl3 {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hn : 1 ≤ n)
    (h : p ^ 2 * (p ^ 4 - 1) = 2 * (2 ^ (3 * n) * ((4 ^ n - 1) * (8 ^ n - 1)))) : False := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hm2 : 2 ≤ 2 ^ n := (show 2 = 2 ^ 1 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hn
  have e3 : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have e4 : 4 ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e8 : 8 ^ n = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hdvd2 := two_pow_dvd_sq_sub_one hodd (k := 3 * n)
    ⟨(4 ^ n - 1) * (8 ^ n - 1), by rw [h, pow_succ]; ring⟩
  rw [e3, e4, e8] at h
  rw [e3] at hdvd2
  set m := 2 ^ n with hm
  have h16 : 16 ≤ p ^ 2 := by nlinarith
  have hx : m ^ 3 + 1 ≤ p ^ 2 := by
    have := Nat.le_of_dvd (by omega) hdvd2
    omega
  have hR : 2 * (m ^ 3 * ((m ^ 2 - 1) * (m ^ 3 - 1))) ≤ m ^ 9 := by
    calc 2 * (m ^ 3 * ((m ^ 2 - 1) * (m ^ 3 - 1))) ≤ 2 * (m ^ 3 * (m ^ 2 * m ^ 3)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _)
            (Nat.sub_le _ _)))
      _ = 2 * m ^ 8 := by ring
      _ ≤ m * m ^ 8 := Nat.mul_le_mul_right _ hm2
      _ = m ^ 9 := by ring
  have hL : m ^ 9 < p ^ 2 * (p ^ 4 - 1) := by
    have hp4 : m ^ 6 ≤ p ^ 4 - 1 := by
      have : (m ^ 3 + 1) ^ 2 ≤ (p ^ 2) ^ 2 := Nat.pow_le_pow_left hx 2
      have : m ^ 6 + 1 ≤ p ^ 4 := by nlinarith
      omega
    have h6 : 0 < m ^ 6 := by positivity
    calc m ^ 9 < (m ^ 3 + 1) * m ^ 6 := by
          rw [show (m ^ 3 + 1) * m ^ 6 = m ^ 9 + m ^ 6 by ring]
          omega
      _ ≤ p ^ 2 * (p ^ 4 - 1) := Nat.mul_le_mul hx hp4
  omega

theorem not_c27Order_psl_p2 {p N : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hN : 2 * N = p ^ 2 * (p ^ 4 - 1)) : ¬ C27Order N := by
  intro h
  rcases h with ⟨n, hn, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨n, hn, rfl⟩ | rfl
  · exact not_psl_p2_eq_sl2 hp hp3 hn hN.symm
  rotate_left 7
  · exact not_psl_p2_eq_sl3 hp hp3 hn hN.symm
  all_goals
    have hp17 : p ≤ 17 := by
      by_contra hp17
      have h1 : 324 ≤ p ^ 2 := by nlinarith
      have h2 : 104976 ≤ p ^ 4 := by nlinarith
      have : 324 * 104975 ≤ p ^ 2 * (p ^ 4 - 1) := Nat.mul_le_mul h1 (by omega)
      omega
    interval_cases p <;> norm_num at hN

theorem not_c27Order_j1 : ¬ C27Order 175560 := by
  intro h
  rcases h with ⟨n, hn, h⟩ | h | h | h | h | h | h | h | ⟨n, hn, h⟩ | h
  · rcases Nat.lt_or_ge n 6 with hn6 | hn6
    · interval_cases n <;> norm_num at h
    · have h1 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
      have h2 : 4 ^ 6 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
      have : 2 ^ 6 * (4 ^ 6 - 1) ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h1 (by omega)
      norm_num at this
      omega
  rotate_left 7
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · interval_cases n <;> norm_num at h
    · have h1 : 2 ^ 9 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 4 ^ 3 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      have h3 : 8 ^ 3 ≤ 8 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      have : 2 ^ 9 * ((4 ^ 3 - 1) * (8 ^ 3 - 1)) ≤ 2 ^ (3 * n) * ((4 ^ n - 1) * (8 ^ n - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))
      norm_num at this
      omega
  all_goals norm_num at h

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
