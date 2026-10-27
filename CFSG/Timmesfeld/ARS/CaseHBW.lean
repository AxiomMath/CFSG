module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Timmesfeld.ARS.CaseH

open Polynomial

variable {E : Type*} [Field E] [Fintype E]

theorem choose_mul_coeff_eq_zero {P : E[X]} (hdeg : P.natDegree < Fintype.card E)
    (hadd : ∀ x y, P.eval (x + y) = P.eval x + P.eval y) {i k : ℕ} (hi : 0 < i) (hik : i < k) :
    (k.choose i : E) * P.coeff k = 0 := by
  classical
  have htaylor : ∀ y, taylor y P = P + C (P.eval y) := by
    intro y
    have h0 : taylor y P - P - C (P.eval y) = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ
        (fun x _ => ?_) ?_
      · simp [taylor_eval, hadd]
      · rw [Finset.card_univ]
        refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
        rw [natDegree_C, Nat.max_zero]
        refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
        rw [natDegree_taylor, max_self]
        exact hdeg
    rw [sub_sub, sub_eq_zero] at h0
    exact h0
  have hconst : hasseDeriv i P = C (P.coeff i) := by
    have h0 : hasseDeriv i P - C (P.coeff i) = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ
        (fun y _ => ?_) ?_
      · have := congrArg (fun Q => Q.coeff i) (htaylor y)
        simp only [taylor_coeff, coeff_add, coeff_C, Nat.pos_iff_ne_zero.1 hi, ite_false,
          add_zero] at this
        simp [this]
      · rw [Finset.card_univ]
        refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
        rw [natDegree_C, Nat.max_zero]
        exact lt_of_le_of_lt ((natDegree_hasseDeriv_le P i).trans (Nat.sub_le _ _)) hdeg
    exact sub_eq_zero.1 h0
  have := congrArg (fun Q => Q.coeff (k - i)) hconst
  simp only [hasseDeriv_coeff, coeff_C, Nat.sub_add_cancel hik.le] at this
  rw [this, ite_eq_right (by omega)]

omit [Fintype E] in
theorem natCast_eq_one_of_odd [CharP E 2] {n : ℕ} (hn : n % 2 = 1) : (n : E) = 1 := by
  rw [CharP.cast_eq_mod E 2 n, hn, Nat.cast_one]

theorem choose_odd_one {a c : ℕ} (hc : 1 ≤ c) :
    (2 ^ a * (1 + 2 ^ c)).choose (2 ^ a) % 2 = 1 := by
  have h := @Choose.choose_pow_mul_pow_mul_modEq_choose_nat a (1 + 2 ^ c) 1 2 ⟨Nat.prime_two⟩
  rw [mul_one, Nat.choose_one_right] at h
  rw [h]
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [pow_succ, mul_comm]
  omega

theorem choose_odd_two {a c w : ℕ} (hc : 1 ≤ c) (hw : w % 2 = 1) :
    (2 ^ a * (1 + 2 ^ c * w)).choose (2 ^ a * (1 + 2 ^ c)) % 2 = 1 := by
  have h := @Choose.choose_pow_mul_pow_mul_modEq_choose_nat a (1 + 2 ^ c * w) (1 + 2 ^ c) 2
    ⟨Nat.prime_two⟩
  rw [h]
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have h2 := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (1 + 2 ^ (c' + 1) * w)
    (1 + 2 ^ (c' + 1)) 2 ⟨Nat.prime_two⟩
  have r1 : 1 + 2 ^ (c' + 1) * w = 1 + 2 * (2 ^ c' * w) := by ring
  have r2 : 1 + 2 ^ (c' + 1) = 1 + 2 * 2 ^ c' := by ring
  have e1 : (1 + 2 ^ (c' + 1) * w) % 2 = 1 := by rw [r1]; omega
  have e2 : (1 + 2 ^ (c' + 1)) % 2 = 1 := by rw [r2]; omega
  have e3 : (1 + 2 ^ (c' + 1) * w) / 2 = 2 ^ c' * w := by rw [r1]; omega
  have e4 : (1 + 2 ^ (c' + 1)) / 2 = 2 ^ c' * 1 := by rw [r2, mul_one]; omega
  rw [e1, e2, e3, e4, Nat.choose_self, one_mul] at h2
  have h3 := @Choose.choose_pow_mul_pow_mul_modEq_choose_nat c' w 1 2 ⟨Nat.prime_two⟩
  rw [Nat.choose_one_right] at h3
  rw [h2, h3, hw]

theorem exponent_of_additive_polar [CharP E 2] {d : ℕ} (hd0 : d ≠ 0) (hdE : d < Fintype.card E)
    (hadd : ∀ x y : E, (x + y + 1) ^ d - (x + y) ^ d - 1 =
      ((x + 1) ^ d - x ^ d - 1) + ((y + 1) ^ d - y ^ d - 1)) :
    (∃ a, d = 2 ^ a) ∨ ∃ a b, a < b ∧ d = 2 ^ a + 2 ^ b := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨a, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd0
  have ho1 : o ≠ 1 := fun h => hne.1 a (by rw [h, mul_one])
  have ho3 : 3 ≤ o := by obtain ⟨r, rfl⟩ := ho; omega
  obtain ⟨c, w, hw, hcw⟩ := Nat.exists_eq_two_pow_mul_odd (show o - 1 ≠ 0 by omega)
  have hc : 1 ≤ c := by
    by_contra h0
    have : c = 0 := by omega
    rw [this, pow_zero, one_mul] at hcw
    obtain ⟨r, rfl⟩ := ho
    obtain ⟨r', rfl⟩ := hw
    omega
  have hw1 : w ≠ 1 := fun h => hne.2 a (a + c) (by omega) (by
    rw [show o = 1 + 2 ^ c * w by omega, h, mul_one, mul_add, mul_one, pow_add])
  have hw3 : 3 ≤ w := by obtain ⟨r, rfl⟩ := hw; omega
  have hwo : w % 2 = 1 := by obtain ⟨r, rfl⟩ := hw; omega
  have hod : o = 1 + 2 ^ c * w := by omega
  subst hod
  set d := 2 ^ a * (1 + 2 ^ c * w) with hd
  set P : E[X] := (X + 1) ^ d - X ^ d - 1 with hP
  have hPdeg : P.natDegree < Fintype.card E := by
    refine lt_of_le_of_lt ?_ hdE
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (natDegree_pow_le).trans (by
        rw [show (X + 1 : E[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one])
    · exact (natDegree_X_pow_le d)
    · rw [natDegree_one]; exact Nat.zero_le _
  have hPadd : ∀ x y, P.eval (x + y) = P.eval x + P.eval y := by
    intro x y
    simp only [hP, eval_sub, eval_pow, eval_add, eval_X, eval_one]
    exact hadd x y
  set k := 2 ^ a * (1 + 2 ^ c) with hk
  have hpos2 : 0 < 2 ^ a := pow_pos (by norm_num) _
  have hik : 2 ^ a < k := by
    rw [hk]
    have : 0 < 2 ^ c := pow_pos (by norm_num) _
    nlinarith
  have hkd : k < d := by
    rw [hk, hd]
    have : 0 < 2 ^ c := pow_pos (by norm_num) _
    apply Nat.mul_lt_mul_of_pos_left _ hpos2
    nlinarith
  have hcoeff : P.coeff k = (d.choose k : E) := by
    simp only [hP, coeff_sub, coeff_X_add_one_pow, coeff_X_pow, coeff_one,
      ite_eq_right (Nat.ne_of_lt hkd), ite_eq_right (by omega : k ≠ 0), sub_zero]
  have := choose_mul_coeff_eq_zero hPdeg hPadd hpos2 hik
  rw [hcoeff, natCast_eq_one_of_odd (choose_odd_one hc), natCast_eq_one_of_odd
    (choose_odd_two hc hwo), one_mul] at this
  exact one_ne_zero this

end CFSG.Timmesfeld.ARS.CaseH
