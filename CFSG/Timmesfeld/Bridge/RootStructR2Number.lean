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
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Timmesfeld.Bridge

theorem eq_of_dvd_two_pow {M s : ℕ} (hM : 2 ≤ M) (hsM : s ≤ M)
    (hdvd : ((2 : ℤ) ^ M - 1) ∣ ((2 : ℤ) ^ s - 1) * ((2 : ℤ) ^ s - 2)) :
    s = 0 ∨ s = 1 ∨ s = M := by
  by_contra hne
  push Not at hne
  obtain ⟨hs0, hs1, hsM'⟩ := hne
  have hs2 : 2 ≤ s := by omega
  have hsM1 : s + 1 ≤ M := by omega
  set x : ℤ := 2 ^ s with hx
  set X : ℤ := 2 ^ M with hX
  have hx4 : 4 ≤ x := by
    have : (2:ℤ) ^ 2 ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hs2
    simpa using this
  have h2x : 2 * x ≤ X := by
    have : (2:ℤ) ^ (s + 1) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hsM1
    rw [pow_succ] at this
    linarith
  rcases lt_or_ge (2 * s) M with hlt | hge
  ·
    have hsq : x * x * 2 ≤ X := by
      have : (2:ℤ) ^ (2 * s + 1) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hlt
      rw [pow_succ, two_mul, pow_add] at this
      exact this
    have hpos : 0 < (x - 1) * (x - 2) := by nlinarith
    have hle := Int.le_of_dvd hpos hdvd
    nlinarith
  · obtain ⟨e, he⟩ : ∃ e, 2 * s = M + e := ⟨2 * s - M, by omega⟩
    set y : ℤ := 2 ^ e with hy
    have hxy : x * x = X * y := by
      rw [hx, hX, hy, ← pow_add, ← pow_add, ← two_mul, he]
    have hey : e + 1 ≤ s := by omega
    have hy2 : 2 * y ≤ x := by
      have : (2:ℤ) ^ (e + 1) ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hey
      rw [pow_succ] at this
      linarith
    have hy1 : 1 ≤ y := one_le_pow₀ (by norm_num)
    have hdvd' : (X - 1) ∣ 3 * x - y - 2 := by
      have : 3 * x - y - 2 = (X - 1) * y - (x - 1) * (x - 2) := by nlinarith
      rw [this]
      exact dvd_sub (dvd_mul_right _ _) hdvd
    obtain ⟨j, hj⟩ := hdvd'
    have hX8 : 8 ≤ X := by nlinarith
    have hj1 : j = 1 := by
      have hjpos : 0 < j := by
        by_contra hj0
        push Not at hj0
        nlinarith
      have hjlt : j < 2 := by
        by_contra hj2
        push Not at hj2
        nlinarith
      omega
    rw [hj1, mul_one] at hj
    have he0 : e = 0 := by
      by_contra he0
      have hyeven : (2:ℤ) ∣ y := by
        rw [hy]
        exact dvd_pow_self 2 he0
      have hxeven : (2:ℤ) ∣ x := by rw [hx]; exact dvd_pow_self 2 (by omega)
      have hXeven : (2:ℤ) ∣ X := by rw [hX]; exact dvd_pow_self 2 (by omega)
      omega
    rw [he0, pow_zero] at hy
    rw [hy, mul_one] at hxy
    have : (x - 1) * (x - 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h <;> linarith

theorem false_of_sub_mul_eq {x Y w : ℤ} (hx4 : 4 ≤ x) (hY : 0 < Y) (hw1 : 1 ≤ w) (hwY : w < Y)
    (heq : (Y - w) * (3 * x - 1 + x * x * w) = x * x * Y + 1) : False := by
  have key : x * x * (Y * (w - 1) - w * w) + (3 * x - 1) * (Y - w) = 1 := by nlinarith
  rcases eq_or_lt_of_le hw1 with hw | hw
  · subst hw
    have h1 : (3 * x - 1) * Y = x * (x + 3) := by nlinarith
    have hxY : x ∣ Y := by
      have h2 : x ∣ (3 * x - 1) * Y := ⟨x + 3, by rw [h1]⟩
      have h3 : x ∣ 3 * x * Y := ⟨3 * Y, by ring⟩
      have : Y = 3 * x * Y - (3 * x - 1) * Y := by ring
      rw [this]
      exact dvd_sub h3 h2
    have hYx : x ≤ Y := Int.le_of_dvd hY hxY
    nlinarith
  · rcases lt_or_eq_of_le (show w ≤ Y - 1 by omega) with hw' | hw'
    · have hY4 : 4 ≤ Y := by omega
      have hnn : 0 ≤ Y * (w - 1) - w * w := by nlinarith
      have hpos : 0 ≤ x * x * (Y * (w - 1) - w * w) := by positivity
      nlinarith
    · subst hw'
      nlinarith

theorem false_of_three_le {M s : ℕ} {X x t T : ℤ} (hM : 2 ≤ M) (hX : X = 2 ^ M)
    (hx : x = 2 ^ s) (ht3 : 3 ≤ t) (hT0 : 0 ≤ T) (htT : X + 1 = t * T) (hk : x * t ≤ X)
    (hdvd : (X - 1) ∣ (x * t - 1) * (x * t - 2)) : False := by
  have hX4 : 4 ≤ X := by
    have : (2:ℤ) ^ 2 ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
    rw [hX]; simpa using this
  have hx1 : 1 ≤ x := by rw [hx]; exact one_le_pow₀ (by norm_num)
  have hXeven : (2:ℤ) ∣ X := by rw [hX]; exact dvd_pow_self 2 (by omega)
  have hodd : ¬ (2:ℤ) ∣ t * T := by rw [← htT]; omega
  have htodd : ¬ (2:ℤ) ∣ t := fun h' => hodd (dvd_mul_of_dvd_left h' _)
  have hTodd : ¬ (2:ℤ) ∣ T := fun h' => hodd (dvd_mul_of_dvd_right h' _)
  have hT1 : 1 ≤ T := by
    rcases eq_or_lt_of_le hT0 with h0 | h0
    · rw [← h0, mul_zero] at htT; omega
    · omega
  have hT3 : 3 ≤ T := by
    by_contra hT
    have hT1' : T = 1 := by omega
    rw [hT1', mul_one] at htT
    nlinarith
  have h3T : 3 * T ≤ X + 1 := by rw [htT]; nlinarith
  have hcop : IsCoprime (X - 1) t := by
    obtain ⟨w, hw⟩ : ∃ w : ℤ, t = 2 * w + 1 := ⟨t / 2, by omega⟩
    exact ⟨w, 1 - w * T, by linear_combination w * htT + hw⟩
  have hV : (X - 1) ∣ T - x * (X + 2 - x * t) := by
    refine hcop.dvd_of_dvd_mul_right ?_
    have : t * (T - x * (X + 2 - x * t)) = (x * t - 1) * (x * t - 2) - (x * t - 1) * (X - 1) := by
      linear_combination -htT
    rw [mul_comm, this]
    exact dvd_sub hdvd (dvd_mul_left _ _)
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s
    ·
      rw [hx, pow_zero] at hV hk
      have hW : (X - 1) ∣ T + t - 3 := by
        have : T + t - 3 = (T - 1 * (X + 2 - 1 * t)) + (X - 1) := by ring
        rw [this]
        exact dvd_add hV (dvd_refl _)
      have hpos : 0 < T + t - 3 := by omega
      have hle := Int.le_of_dvd hpos hW
      nlinarith
    ·
      rw [hx, pow_one] at hV hk
      have hW : (X - 1) ∣ T + 4 * t - 6 := by
        have : T + 4 * t - 6 = (T - 2 * (X + 2 - 2 * t)) + 2 * (X - 1) := by ring
        rw [this]
        exact dvd_add hV (dvd_mul_left _ _)
      obtain ⟨j, hj⟩ := hW
      have hj0 : 0 < j := by
        by_contra hj0
        push Not at hj0
        nlinarith
      have hj3 : j < 3 := by
        by_contra hj3
        push Not at hj3
        nlinarith
      interval_cases j
      ·
        have hT : T = X + 5 - 4 * t := by linarith
        rw [hT] at htT
        have : (t - 1) * (X - (4 * t - 1)) = 0 := by linear_combination -htT
        rcases mul_eq_zero.1 this with h' | h' <;> omega
      ·
        exact hTodd ⟨X + 2 - 2 * t, by linarith⟩
  ·
    have hx4 : 4 ≤ x := by
      have : (2:ℤ) ^ 2 ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hs
      rw [hx]; simpa using this
    have hxeven : (2:ℤ) ∣ x := by rw [hx]; exact dvd_pow_self 2 (by omega)
    have hsM : s + 2 ≤ M := by
      by_contra hsM
      push Not at hsM
      have : (2:ℤ) ^ M ≤ 2 ^ (s + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_succ, ← hX, ← hx] at this
      nlinarith
    have h4x : 4 * x ≤ X := by
      have : (2:ℤ) ^ (s + 2) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hsM
      rw [pow_add, ← hX, ← hx] at this
      linarith
    rcases lt_or_ge M (2 * s) with hlt | hge
    ·
      obtain ⟨e, he⟩ : ∃ e, 2 * s = M + e := ⟨2 * s - M, by omega⟩
      have he1 : 1 ≤ e := by omega
      obtain ⟨y, hy⟩ : ∃ y : ℤ, y = 2 ^ e := ⟨_, rfl⟩
      have hxy : x * x = X * y := by rw [hx, hX, hy, ← pow_add, ← pow_add, ← two_mul, he]
      have hyeven : (2:ℤ) ∣ y := by rw [hy]; exact dvd_pow_self 2 (by omega)
      have hy0 : 0 < y := by rw [hy]; positivity
      have hW : (X - 1) ∣ T - 3 * x + y * t := by
        have : T - 3 * x + y * t = (T - x * (X + 2 - x * t)) + (X - 1) * (x - y * t) := by
          linear_combination (-t) * hxy
        rw [this]
        exact dvd_add hV (dvd_mul_right _ _)
      have hyt : y * t ≤ x := by nlinarith
      have hW0 : T - 3 * x + y * t = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd hW ?_
        rw [abs_lt]
        constructor <;> nlinarith
      obtain ⟨a, ha⟩ := hxeven
      obtain ⟨b, hb⟩ := hyeven
      exact hTodd ⟨3 * a - b * t, by rw [ha, hb] at hW0; linarith⟩
    ·
      obtain ⟨L, hL⟩ : ∃ L, M = 2 * s + L := ⟨M - 2 * s, by omega⟩
      obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = 2 ^ L := ⟨_, rfl⟩
      have hXY : X = x * x * Y := by rw [hX, hx, hY, ← pow_add, ← pow_add, ← two_mul, hL]
      have hY0 : 0 < Y := by rw [hY]; positivity
      obtain ⟨h, w, hhw, hw0, hwY⟩ : ∃ h w : ℤ, t + w = h * Y ∧ 0 ≤ w ∧ w < Y := by
        refine ⟨(t + Y - 1) / Y, (t + Y - 1) / Y * Y - t, by ring, ?_, ?_⟩
        · have := Int.mul_ediv_add_emod (t + Y - 1) Y
          have h1 := Int.emod_lt_of_pos (t + Y - 1) hY0
          nlinarith
        · have := Int.mul_ediv_add_emod (t + Y - 1) Y
          have h1 := Int.emod_nonneg (t + Y - 1) hY0.ne'
          nlinarith
      have htY : t ≤ x * Y := by nlinarith
      have hh1 : 1 ≤ h := by nlinarith
      have hhx : h ≤ x := by nlinarith
      have hW : (X - 1) ∣ T - 3 * x + h - x * x * w := by
        have : T - 3 * x + h - x * x * w =
            (T - x * (X + 2 - x * t)) - (X - 1) * (h - x) := by
          linear_combination (-(x * x)) * hhw + h * hXY
        rw [this]
        exact dvd_sub hV (dvd_mul_right _ _)
      have hxxw : x * x * w ≤ X - x * x := by
        have : x * x * w ≤ x * x * (Y - 1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        linarith
      have hxxw0 : 0 ≤ x * x * w := by positivity
      have hq : 0 < x * x - 3 * x + 3 := by
        have h1 : (x - 2) * (x - 1) = x * x - 3 * x + 2 := by ring
        have h2 : 0 ≤ (x - 2) * (x - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hW0 : T - 3 * x + h - x * x * w = 0 :=
        Int.eq_zero_of_abs_lt_dvd hW (abs_lt.2 ⟨by linarith, by linarith⟩)
      have hT : T = 3 * x - h + x * x * w := by linarith
      rcases eq_or_lt_of_le hw0 with hw | hw
      ·
        rw [← hw, add_zero] at hhw
        have hL0 : L = 0 := by
          by_contra hL0
          apply htodd
          rw [hhw, hY]
          exact dvd_mul_of_dvd_right (dvd_pow_self 2 hL0) _
        rw [hL0, pow_zero] at hY
        rw [hY, mul_one] at hhw hXY
        rw [← hw, mul_zero, add_zero] at hT
        rw [hT, hXY, ← hhw] at htT
        obtain ⟨z, hz⟩ : (4:ℤ) ∣ x := by
          rw [hx, show s = 2 + (s - 2) by omega, pow_add]
          exact dvd_mul_right _ _
        obtain ⟨u, hu⟩ : ∃ u : ℤ, t = 2 * u + 1 := ⟨t / 2, by omega⟩
        have : 2 + 4 * (4 * z ^ 2 - 6 * u * z - 3 * z + u ^ 2 + u) = 0 := by
          rw [hz, hu] at htT
          linear_combination htT
        omega
      · have hw1 : 1 ≤ w := hw
        rcases eq_or_lt_of_le hh1 with hh | hh
        ·
          rw [← hh] at hhw hT
          have ht : t = Y - w := by linarith
          apply false_of_sub_mul_eq hx4 hY0 hw1 hwY
          rw [← ht, show 3 * x - 1 + x * x * w = T by rw [hT], ← htT, hXY]
        ·
          have h2Y : 2 * Y ≤ h * Y := mul_le_mul_of_nonneg_right (by omega) hY0.le
          have ht : Y + 1 ≤ t := by linarith
          have hxxw' : x * x ≤ x * x * w := le_mul_of_one_le_right (by positivity) hw1
          have hT' : x * x + 2 * x ≤ T := by linarith
          have hprod : (Y + 1) * (x * x + 2 * x) ≤ t * T :=
            mul_le_mul ht hT' (by positivity) (by linarith)
          have hexp : (Y + 1) * (x * x + 2 * x) = x * x * Y + 2 * x * Y + x * x + 2 * x := by
            ring
          have hxY : 0 ≤ x * Y := by positivity
          have hxx : 16 ≤ x * x := by
            have := mul_le_mul hx4 hx4 (by norm_num) (by linarith)
            linarith
          linarith

theorem eq_of_dvd_sub_one_mul_sub_two {M k : ℕ} (hM : 2 ≤ M) (hk1 : 1 ≤ k) (hkM : k ≤ 2 ^ M)
    (hko : ∃ s t : ℕ, k = 2 ^ s * t ∧ t ∣ 2 ^ M + 1)
    (hdvd : ((2 : ℤ) ^ M - 1) ∣ ((k : ℤ) - 1) * ((k : ℤ) - 2)) :
    k = 1 ∨ k = 2 ∨ k = 2 ^ M := by
  obtain ⟨s, t, rfl, htQ⟩ := hko
  obtain ⟨T, hT⟩ := htQ
  have ht0 : t ≠ 0 := by rintro rfl; simp at hk1
  have htodd : ¬ 2 ∣ t := by
    rintro ⟨u, rfl⟩
    have : (2 : ℕ) ∣ 2 ^ M + 1 := ⟨u * T, by rw [hT]; ring⟩
    have h2 : (2 : ℕ) ∣ 2 ^ M := dvd_pow_self 2 (by omega)
    omega
  rcases (show t = 1 ∨ 3 ≤ t by omega) with rfl | ht3
  ·
    have hsM : s ≤ M := by
      rw [mul_one] at hkM
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hkM
    push_cast at hdvd
    rw [mul_one] at hdvd
    rcases eq_of_dvd_two_pow hM hsM hdvd with rfl | rfl | rfl <;> simp
  · exfalso
    refine false_of_three_le (s := s) hM rfl rfl (t := t) (T := T) (by exact_mod_cast ht3)
      (by positivity) (by exact_mod_cast hT) (by exact_mod_cast hkM) ?_
    push_cast at hdvd
    exact hdvd

end CFSG.Timmesfeld.Bridge
