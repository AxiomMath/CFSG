module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.NumberTheory

theorem dvd_sub_one_of_dvd_odd_pow_sub_one {d Q p : ℕ} (hd : d ∣ 3 ∨ d ∣ 4)
    (hp : Odd p) (hQ : Odd Q) (h : d ∣ Q ^ p - 1) : d ∣ Q - 1 := by
  have hdpos : 0 < d := by
    rcases hd with h | h
    · exact Nat.pos_of_dvd_of_pos h (by norm_num)
    · exact Nat.pos_of_dvd_of_pos h (by norm_num)
  have hdle : d ≤ 4 := by
    rcases hd with h | h
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) h
  obtain ⟨m, hm⟩ := hQ
  interval_cases d
  · exact one_dvd _
  · exact ⟨m, by omega⟩
  ·
    have h3 : Q ^ p % 3 = 1 := by
      have h0 : (Q ^ p - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      have hQp : 1 ≤ Q ^ p := Nat.one_le_pow _ _ (by omega)
      omega
    obtain ⟨k, rfl⟩ := hp
    have hQ1 : Q % 3 = 1 := by
      have hlt : Q % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hq : Q % 3
      · rw [Nat.pow_mod, hq] at h3
        norm_num at h3
      · rfl
      · rw [Nat.pow_mod, hq] at h3
        have h4 : 2 ^ (2 * k + 1) % 3 = 2 := by
          rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        rw [h4] at h3
        norm_num at h3
    omega
  ·
    have h8 : 4 ∣ Q ^ 2 - 1 :=
      (by norm_num : 4 ∣ 8).trans (Nat.eight_dvd_sq_sub_one_of_odd ⟨m, hm⟩)
    have hsq : Q ^ 2 % 4 = 1 := by
      have h0 : (Q ^ 2 - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8
      have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have h4 : Q ^ p % 4 = 1 := by
      have h0 : (Q ^ p - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      have hQp : 1 ≤ Q ^ p := Nat.one_le_pow _ _ (by omega)
      omega
    obtain ⟨k, rfl⟩ := hp
    have hQ1 : Q % 4 = 1 := by
      have hpm : Q ^ (2 * k + 1) % 4 = Q % 4 := by
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, hsq]
        norm_num
      rw [hpm] at h4
      exact h4
    omega

theorem dvd_add_one_of_dvd_odd_pow_add_one {d Q p : ℕ} (hd : d ∣ 3 ∨ d ∣ 4)
    (hp : Odd p) (hQ : Odd Q) (h : d ∣ Q ^ p + 1) : d ∣ Q + 1 := by
  have hdpos : 0 < d := by
    rcases hd with h | h
    · exact Nat.pos_of_dvd_of_pos h (by norm_num)
    · exact Nat.pos_of_dvd_of_pos h (by norm_num)
  have hdle : d ≤ 4 := by
    rcases hd with h | h
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) h
  obtain ⟨m, hm⟩ := hQ
  interval_cases d
  · exact one_dvd _
  · exact ⟨m + 1, by omega⟩
  ·
    have h3 : Q ^ p % 3 = 2 := by
      have h0 : (Q ^ p + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      have hQp : 1 ≤ Q ^ p := Nat.one_le_pow _ _ (by omega)
      omega
    obtain ⟨k, rfl⟩ := hp
    have hQ2 : Q % 3 = 2 := by
      have hlt : Q % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hq : Q % 3
      · rw [Nat.pow_mod, hq] at h3
        norm_num at h3
      · rw [Nat.pow_mod, hq] at h3
        norm_num at h3
      · rfl
    omega
  ·
    have h8 : 4 ∣ Q ^ 2 - 1 :=
      (by norm_num : 4 ∣ 8).trans (Nat.eight_dvd_sq_sub_one_of_odd ⟨m, hm⟩)
    have hsq : Q ^ 2 % 4 = 1 := by
      have h0 : (Q ^ 2 - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8
      have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have h4 : Q ^ p % 4 = 3 := by
      have h0 : (Q ^ p + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      have hQp : 1 ≤ Q ^ p := Nat.one_le_pow _ _ (by omega)
      omega
    have hQ3 : Q % 4 = 3 := by
      have hpm : Q ^ p % 4 = Q % 4 := by
        obtain ⟨k, rfl⟩ := hp
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, hsq]
        norm_num
      rw [hpm] at h4
      have hlt : Q % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases hq : Q % 4
      · norm_num at h4
      · norm_num at h4
      · omega
      · rfl
    omega

theorem gcd_four_add_one {Q : ℕ} (hQ : Odd Q) :
    Nat.gcd 4 (Q + 1) = if 4 ∣ Q + 1 then 4 else 2 := by
  have hle : Nat.gcd 4 (Q + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have heven : 2 ∣ Nat.gcd 4 (Q + 1) := by
    refine Nat.dvd_gcd (by norm_num) ?_
    obtain ⟨m, hm⟩ := hQ
    exact ⟨m + 1, by omega⟩
  split_ifs with h
  · exact Nat.gcd_eq_left_iff_dvd.mpr h
  · set g := Nat.gcd 4 (Q + 1) with hg
    have hg2 : 2 ∣ g := hg.symm ▸ heven
    have hg0 : 0 < g := Nat.pos_of_dvd_of_pos (hg.symm ▸ Nat.gcd_dvd_left 4 (Q + 1))
      (by norm_num)
    have hgdiv : g ∣ 4 := hg.symm ▸ Nat.gcd_dvd_left 4 (Q + 1)
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp hgdiv
    interval_cases k
    · rw [hk] at hg2; norm_num at hg2
    · rw [hk]; norm_num
    · exfalso
      apply h
      have hgd : g ∣ Q + 1 := hg.symm ▸ Nat.gcd_dvd_right 4 (Q + 1)
      rw [hk] at hgd
      norm_num at hgd
      exact hgd

end CFSG.NumberTheory

end
