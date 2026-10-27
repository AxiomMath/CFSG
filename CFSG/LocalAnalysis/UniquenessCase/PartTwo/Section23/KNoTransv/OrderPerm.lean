module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs

import CFSG.Quasithin.Recognition.F112Crit.McLOrders
public import Mathlib.Data.Nat.Prime.Factorial

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

private theorem two_mul_eight_pow_le_factorial {n : ℕ} (hn : 16 ≤ n) :
    2 * 8 ^ (n - 2) ≤ n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k _ ih =>
    have he : 2 * 8 ^ (k + 1 - 2) = (2 * 8 ^ (k - 2)) * 8 := by
      rw [show k + 1 - 2 = k - 2 + 1 by omega, pow_succ]
      ring
    rw [he, Nat.factorial_succ]
    calc (2 * 8 ^ (k - 2)) * 8 = 8 * (2 * 8 ^ (k - 2)) := by ring
      _ ≤ (k + 1) * (2 * 8 ^ (k - 2)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left _ ih

private theorem false_of_small {m N n : ℕ} (hNv : N + 1 = padicValNat 2 n.factorial)
    (hm : m = n.factorial / 2) (hmlt : m < 2 ^ (3 * N)) (hn11 : 11 ≤ n) (hn15 : n ≤ 15) :
    False := by
  interval_cases n
  · have hpad : padicValNat 2 (Nat.factorial 11) = 8 := by
      rw [show Nat.factorial 11 = 2 ^ 8 * 155925 by norm_num,
        Nat.maxPowDiv.base_pow_mul (by norm_num : 1 < 2) (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.zero_add]
    rw [hpad] at hNv
    have hN : N = 7 := by omega
    rw [hm, hN] at hmlt
    norm_num at hmlt
  · have hpad : padicValNat 2 (Nat.factorial 12) = 10 := by
      rw [show Nat.factorial 12 = 2 ^ 10 * 467775 by norm_num,
        Nat.maxPowDiv.base_pow_mul (by norm_num : 1 < 2) (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.zero_add]
    rw [hpad] at hNv
    have hN : N = 9 := by omega
    rw [hm, hN] at hmlt
    norm_num at hmlt
  · have hpad : padicValNat 2 (Nat.factorial 13) = 10 := by
      rw [show Nat.factorial 13 = 2 ^ 10 * 6081075 by norm_num,
        Nat.maxPowDiv.base_pow_mul (by norm_num : 1 < 2) (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.zero_add]
    rw [hpad] at hNv
    have hN : N = 9 := by omega
    rw [hm, hN] at hmlt
    norm_num at hmlt
  · have hpad : padicValNat 2 (Nat.factorial 14) = 11 := by
      rw [show Nat.factorial 14 = 2 ^ 11 * 42567525 by norm_num,
        Nat.maxPowDiv.base_pow_mul (by norm_num : 1 < 2) (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.zero_add]
    rw [hpad] at hNv
    have hN : N = 10 := by omega
    rw [hm, hN] at hmlt
    norm_num at hmlt
  · have hpad : padicValNat 2 (Nat.factorial 15) = 11 := by
      rw [show Nat.factorial 15 = 2 ^ 11 * 638512875 by norm_num,
        Nat.maxPowDiv.base_pow_mul (by norm_num : 1 < 2) (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.zero_add]
    rw [hpad] at hNv
    have hN : N = 10 := by omega
    rw [hm, hN] at hmlt
    norm_num at hmlt

theorem false_of_ordData_factorial {m n : ℕ} (hm : OrdData m) (hmn : m * 2 = n.factorial) :
    False := by
  obtain ⟨N, e, p, ⟨r, hr, hmr⟩, he7, hpp, hpm, _, _, hmlt⟩ := hm
  have hp := hpp.prime
  have hp11 : 11 ≤ p := by
    have hep : e < p := CFSG.Quasithin.F112Crit.McLOrd.primDiv_lt hpp (by omega)
    have hp8 : 8 ≤ p := by omega
    by_contra h
    have hp10 : p ≤ 10 := by omega
    interval_cases p <;> norm_num at hp
  have hpn : p ∣ n.factorial := by
    rw [← hmn]
    exact dvd_mul_of_dvd_left hpm 2
  have hn11 : 11 ≤ n := by
    have h := (hp.dvd_factorial).mp hpn
    omega
  have hNv : N + 1 = padicValNat 2 n.factorial := by
    have h2 : 2 ^ (N + 1) * r = n.factorial := by
      calc 2 ^ (N + 1) * r = 2 ^ N * r * 2 := by rw [pow_succ]; ring
        _ = m * 2 := by rw [← hmr]
        _ = n.factorial := hmn
    rw [← h2, Nat.maxPowDiv.base_pow_mul (by norm_num : 1 < 2) hr.pos.ne',
      padicValNat.eq_zero_of_not_dvd hr.not_two_dvd_nat, Nat.zero_add]
  have hm2 : m = n.factorial / 2 := by
    rw [← hmn, Nat.mul_div_left m (by norm_num : 0 < 2)]
  rcases Nat.lt_or_ge n 16 with hn16 | hn16
  · exact false_of_small hNv hm2 hmlt hn11 (by omega)
  ·
    have hNle : N + 1 < n := by
      rw [hNv]
      exact padicValNat_factorial_lt_of_ne_zero 2 (by omega)
    have h3 : 3 * N ≤ 3 * (n - 2) := by omega
    have hpow : 2 ^ (3 * N) ≤ 8 ^ (n - 2) := by
      have h8 : 8 ^ (n - 2) = 2 ^ (3 * (n - 2)) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, pow_mul]
      rw [h8]
      exact Nat.pow_le_pow_right (by norm_num) h3
    have hlow : 8 ^ (n - 2) ≤ m := by
      have hfac : 2 * 8 ^ (n - 2) ≤ n.factorial := two_mul_eight_pow_le_factorial hn16
      have h2m : n.factorial = 2 * m := by rw [← hmn]; ring
      rw [h2m] at hfac
      exact Nat.le_of_mul_le_mul_left hfac (by norm_num : 0 < 2)
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
