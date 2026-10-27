module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Arith
import Mathlib.NumberTheory.Fermat
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

open CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

theorem two_pow_nine_dvd_of_targetOrder {n M : ℕ} (hn : 3 ≤ n)
    (hM : targetOrder (2 ^ n) M) : 2 ^ 9 ∣ M := by
  have h3 : 2 ^ 9 ∣ (2 ^ n) ^ 3 := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have h4 : (2 ^ n) ^ 3 ∣ (2 ^ n) ^ 4 := pow_dvd_pow _ (by norm_num)
  have h6 : (2 ^ n) ^ 3 ∣ (2 ^ n) ^ 6 := pow_dvd_pow _ (by norm_num)
  rcases hM with h | h | h
  · rw [h]; exact Dvd.dvd.mul_right h3 _
  · rw [h]; exact Dvd.dvd.mul_right (h3.trans h4) _
  · rw [h]; exact Dvd.dvd.mul_right (h3.trans h6) _

theorem nine_dvd_of_targetOrder_of_three_dvd_sub_one {n M : ℕ}
    (hM : targetOrder (2 ^ n) M) (h3 : 3 ∣ 2 ^ n - 1) : 9 ∣ M := by
  have h2 : 3 ∣ (2 ^ n) ^ 2 - 1 := h3.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)
  have h3' : 3 ∣ (2 ^ n) ^ 3 - 1 := h3.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 3)
  have h4 : 3 ∣ (2 ^ n) ^ 4 - 1 := h3.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 4)
  have h23 : 9 ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    rw [show 9 = 3 * 3 by norm_num]
    exact mul_dvd_mul h2 h3'
  have h24 : 9 ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1) := by
    rw [show 9 = 3 * 3 by norm_num]
    exact mul_dvd_mul h2 h4
  rcases hM with h | h | h
  · rw [h]; exact Dvd.dvd.mul_left h23 _
  · rw [h]; exact Dvd.dvd.mul_left h24 _
  · rw [h]
    have h234 : 9 ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) := by
      have hcomm : ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) =
          ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 3 + 1) := by ring
      rw [hcomm]
      exact Dvd.dvd.mul_right h24 _
    exact Dvd.dvd.mul_left h234 _

theorem ne_l2_order_mul_three {n a : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠
      3 * (2 ^ a * ((2 ^ a) ^ 2 - 1)) := by
  intro h
  have hx : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hxea : Even (2 ^ a) := even_two.pow_of_ne_zero (by omega)
  have hxen : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
  have hodd_a : Odd ((2 ^ a) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (pow_pos (by norm_num) a))
      (hxea.pow_of_ne_zero (n := 2) (by norm_num)) (by norm_num)
  have o2 : Odd ((2 ^ n) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (pow_pos (by norm_num) n))
      (hxen.pow_of_ne_zero (n := 2) (by norm_num)) (by norm_num)
  have o3 : Odd ((2 ^ n) ^ 3 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (pow_pos (by norm_num) n))
      (hxen.pow_of_ne_zero (n := 3) (by norm_num)) (by norm_num)
  have h3odd : Odd (3 * ((2 ^ a) ^ 2 - 1)) := by
    have : Odd (3 : ℕ) := by norm_num
    exact this.mul hodd_a
  have h2 : 2 ^ a * (3 * ((2 ^ a) ^ 2 - 1)) =
      2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    calc 2 ^ a * (3 * ((2 ^ a) ^ 2 - 1))
        = 3 * (2 ^ a * ((2 ^ a) ^ 2 - 1)) := by ring
      _ = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := h.symm
      _ = 2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
            rw [← pow_mul]
  obtain ⟨ha3, hodd⟩ := knl_two_pow_mul_odd_inj h3odd (o2.mul o3) h2
  subst ha3
  rw [pow_mul] at hodd
  have hfac : ((2 ^ n) ^ 3) ^ 2 - 1 =
      ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 3 - 1) := by
    have := Nat.sq_sub_sq ((2 ^ n) ^ 3) 1
    simpa using this
  rw [hfac] at hodd
  have hpos : 0 < (2 ^ n) ^ 3 - 1 := by
    have h8 : 8 ≤ (2 ^ n) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hx 3
    omega
  have hcomm : ((2 ^ n) ^ 3 - 1) * (3 * ((2 ^ n) ^ 3 + 1)) =
      ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) := by
    calc ((2 ^ n) ^ 3 - 1) * (3 * ((2 ^ n) ^ 3 + 1))
        = 3 * (((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 3 - 1)) := by ring
      _ = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := hodd
      _ = ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) := by ring
  have hcancel : 3 * ((2 ^ n) ^ 3 + 1) = (2 ^ n) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left hpos hcomm
  have hlt : (2 ^ n) ^ 2 - 1 < 3 * ((2 ^ n) ^ 3 + 1) := by
    have h1 : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : (2 ^ n) ^ 3 < 3 * ((2 ^ n) ^ 3 + 1) := by nlinarith
    omega
  omega

theorem prime_dvd_and_two_pow_le {p e M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (h : p * (p ^ 2 - 1) = 2 ^ (e + 1) * M) : p ∣ M ∧ 2 ^ e ≤ p + 1 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcop : Nat.Coprime p (2 ^ (e + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  refine ⟨?_, ?_⟩
  · have h1 : p ∣ 2 ^ (e + 1) * M := h ▸ dvd_mul_right p _
    exact hcop.dvd_of_dvd_mul_left h1
  · have h2 : 2 ^ (e + 1) ∣ p * (p ^ 2 - 1) := ⟨M, h⟩
    have h3 : 2 ^ (e + 1) ∣ p ^ 2 - 1 := hcop.symm.dvd_of_dvd_mul_left h2
    obtain ⟨u, hu⟩ := hpodd
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    have h4 : p ^ 2 - 1 = 4 * (u * (u + 1)) := by
      have : p ^ 2 = 4 * (u * (u + 1)) + 1 := by rw [hu]; ring
      omega
    have h5 : 2 ^ (f + 1 + 1) = 4 * 2 ^ f := by ring
    rw [h4, h5] at h3
    have h6 : 2 ^ f ∣ u * (u + 1) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
    have key : 2 ^ f ∣ u ∨ 2 ^ f ∣ u + 1 := by
      by_cases hu2 : 2 ∣ u
      · left
        have hc : Nat.Coprime (2 ^ f) (u + 1) :=
          Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨u / 2, by omega⟩)
        exact hc.dvd_of_dvd_mul_right h6
      · right
        have hc : Nat.Coprime (2 ^ f) u :=
          Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨u / 2, by omega⟩)
        exact hc.dvd_of_dvd_mul_left h6
    have h7 : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    rcases key with hk | hk
    · have := Nat.le_of_dvd (by omega) hk
      omega
    · have := Nat.le_of_dvd (by omega) hk
      omega

theorem prime_lt_pow_sub_one {x p k : ℕ} (hx : 3 ≤ x) (hk : 2 ≤ k) (hp : p.Prime)
    (hd : p ∣ x ^ k - 1) : p < x ^ k - 1 := by
  have h9 : 9 ≤ x ^ k := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      _ ≤ x ^ k := Nat.pow_le_pow_left hx k
  have hpos : 0 < x ^ k - 1 := by omega
  have hle : p ≤ x ^ k - 1 := Nat.le_of_dvd hpos hd
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hprime : (x ^ k - 1).Prime := heq ▸ hp
    obtain ⟨hx2, -⟩ := Nat.prime_of_pow_sub_one_prime (a := x) (n := k) (by omega) hprime
    omega

theorem ne_l2odd_order_mul_three {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (h3x : 3 ∣ 2 ^ n - 1) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) * 2 ≠
      3 * (p * (p ^ 2 - 1)) := by
  intro h
  have hx : 3 ≤ 2 ^ n := by
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3_2 : 3 ∣ (2 ^ n) ^ 2 - 1 := h3x.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)
  have h3A0 : 3 ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) :=
    dvd_mul_of_dvd_left h3_2 _
  obtain ⟨A, hA⟩ := h3A0
  have e0 : 2 ^ (n * 3 + 1) * (3 * A) =
      ((2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) * 2 := by
    rw [hA]
    have hpow : 2 ^ (n * 3 + 1) = (2 ^ n) ^ 3 * 2 := by
      rw [pow_succ, ← pow_mul]
    rw [hpow]
    ring
  have he : 2 ^ (n * 3 + 1) * A = p * (p ^ 2 - 1) := by
    have e' : 3 * (2 ^ (n * 3 + 1) * A) = 3 * (p * (p ^ 2 - 1)) := by
      calc 3 * (2 ^ (n * 3 + 1) * A)
          = 2 ^ (n * 3 + 1) * (3 * A) := by ring
        _ = ((2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) * 2 := e0
        _ = 3 * (p * (p ^ 2 - 1)) := h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) e'
  obtain ⟨hpA, hle⟩ := prime_dvd_and_two_pow_le (e := n * 3) hp hp2 (by omega) he.symm
  have hpA0 : p ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    rw [hA]
    exact Dvd.dvd.mul_left hpA 3
  have hle' : (2 ^ n) ^ 3 ≤ p + 1 := by
    rw [← pow_mul]
    exact hle
  have hplt : p < (2 ^ n) ^ 3 - 1 := by
    rcases (Nat.Prime.dvd_mul hp).mp hpA0 with hd | hd
    · have hsmall := prime_lt_pow_sub_one (k := 2) hx (by norm_num) hp hd
      have hlt : (2 ^ n) ^ 2 - 1 < (2 ^ n) ^ 3 - 1 := by
        have hp2lt : (2 ^ n) ^ 2 < (2 ^ n) ^ 3 :=
          Nat.pow_lt_pow_right (by omega) (by norm_num)
        omega
      exact hsmall.trans hlt
    · exact prime_lt_pow_sub_one (k := 3) hx (by norm_num) hp hd
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

end
