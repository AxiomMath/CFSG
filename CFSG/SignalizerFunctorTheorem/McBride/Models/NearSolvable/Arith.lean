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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.NearSolvable

theorem pow_mod_eq_pow_mod_mod {a m n : ℕ} (h : a ^ n % m = 1) (p : ℕ) :
    a ^ p % m = a ^ (p % n) % m := by
  conv_lhs => rw [← Nat.div_add_mod p n, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h]
  rw [one_pow, Nat.mod_mul_mod, one_mul, Nat.mod_mod]

theorem two_pow_mod_three {p : ℕ} (hp : Odd p) : 2 ^ p % 3 = 2 := by
  rw [pow_mod_eq_pow_mod_mod (n := 2) (by norm_num), Nat.odd_iff.mp hp]
  norm_num

theorem two_pow_mod_five {p : ℕ} (hp : Odd p) : 2 ^ p % 5 = 2 ∨ 2 ^ p % 5 = 3 := by
  rw [pow_mod_eq_pow_mod_mod (n := 4) (by norm_num)]
  have h2 : p % 2 = 1 := Nat.odd_iff.mp hp
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h | h <;> rw [h] <;> norm_num

theorem two_pow_mod_nine {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) :
    2 ^ p % 9 = 2 ∨ 2 ^ p % 9 = 5 := by
  rw [pow_mod_eq_pow_mod_mod (n := 6) (by norm_num)]
  rcases hp with h | h <;> rw [h] <;> norm_num

theorem three_pow_sq_mod_sixteen {p : ℕ} (hp : Odd p) : (3 ^ p) ^ 2 % 16 = 9 := by
  rw [← pow_mul, mul_comm, pow_mul, pow_mod_eq_pow_mod_mod (n := 2) (by norm_num),
    Nat.odd_iff.mp hp]
  norm_num

theorem prime_mod_six {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2' : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  have h3' : p % 3 ≠ 0 := fun h =>
    h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)).symm
  omega

section

variable {q : ℕ}

theorem three_dvd_sq_sub_one (h : q % 3 = 2) : 3 ∣ q ^ 2 - 1 := by
  have h1 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem three_dvd_cube_add_one (h : q % 3 = 2) : 3 ∣ q ^ 3 + 1 := by
  have h1 : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, h]
  omega

theorem not_three_dvd_suzuki (h : q % 3 = 2) : ¬ 3 ∣ q ^ 2 * (q ^ 2 + 1) * (q - 1) := by
  intro hd
  have h1 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hd | hd <;> omega
  · omega

theorem five_dvd_sq_add_one (h : q % 5 = 2 ∨ q % 5 = 3) : 5 ∣ q ^ 2 + 1 := by
  have h1 : q ^ 2 % 5 = 4 := by rcases h with h | h <;> rw [Nat.pow_mod, h]
  omega

theorem not_five_dvd_unitary (h : q % 5 = 2 ∨ q % 5 = 3) :
    ¬ 5 ∣ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) := by
  intro hd
  have h1 : q ^ 2 % 5 = 4 := by rcases h with h | h <;> rw [Nat.pow_mod, h]
  have h2 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rcases h with h | h
    · left; rw [Nat.pow_mod, h]
    · right; rw [Nat.pow_mod, h]
  have hprime : Nat.Prime 5 := by norm_num
  rcases hprime.dvd_mul.mp hd with hd | hd
  · rcases hprime.dvd_mul.mp hd with hd | hd <;> omega
  · omega

theorem not_nine_dvd_psl2 (h : q % 9 = 2 ∨ q % 9 = 5) : ¬ 9 ∣ q * (q ^ 2 - 1) := by
  intro hd
  have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h0 : ((q * (q ^ 2 - 1) : ℕ) : ZMod 9) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast [Nat.cast_sub hq] at h0
  have key : ∀ x : ZMod 9, (x.val = 2 ∨ x.val = 5) → x * (x ^ 2 - 1) ≠ 0 := by decide
  refine key (q : ZMod 9) ?_ h0
  rw [ZMod.val_natCast]
  omega

theorem not_eightyone_dvd_unitary (h : q % 9 = 2 ∨ q % 9 = 5) :
    ¬ 81 ∣ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) := by
  intro hd
  have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h0 : ((q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) : ℕ) : ZMod 81) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast [Nat.cast_sub hq] at h0
  have key : ∀ x : ZMod 81, (x.val % 9 = 2 ∨ x.val % 9 = 5) →
      x ^ 3 * (x ^ 3 + 1) * (x ^ 2 - 1) ≠ 0 := by decide
  refine key (q : ZMod 81) ?_ h0
  rw [ZMod.val_natCast]
  omega

end

theorem two_pow_mod_two {p : ℕ} (hp : 1 ≤ p) : 2 ^ p % 2 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hp
  rw [pow_succ]
  omega

theorem two_pow_sq_mod_two {p : ℕ} (hp : 1 ≤ p) : (2 ^ p) ^ 2 % 2 = 0 := by
  rw [Nat.pow_mod, two_pow_mod_two hp]

theorem odd_two_pow_sq_sub_one {p : ℕ} (hp : 1 ≤ p) : Odd ((2 ^ p) ^ 2 - 1) := by
  have h1 := two_pow_sq_mod_two hp
  have h2 : 1 ≤ (2 ^ p) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

theorem not_two_pow_succ_dvd_psl2 {p : ℕ} (hp : 1 ≤ p) :
    ¬ 2 ^ (p + 1) ∣ 2 ^ p * ((2 ^ p) ^ 2 - 1) := by
  rw [pow_succ]
  intro hd
  have h2 := (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos p)).mp hd
  exact (Nat.not_even_iff_odd.mpr (odd_two_pow_sq_sub_one hp)) (even_iff_two_dvd.mpr h2)

theorem not_two_pow_two_mul_succ_dvd_suzuki {p : ℕ} (hp : 1 ≤ p) :
    ¬ 2 ^ (2 * p + 1) ∣ (2 ^ p) ^ 2 * ((2 ^ p) ^ 2 + 1) * (2 ^ p - 1) := by
  have h1 : 2 ^ (2 * p + 1) = (2 ^ p) ^ 2 * 2 := by
    rw [pow_succ, ← pow_mul, mul_comm p 2]
  have hq := two_pow_sq_mod_two hp
  have hq1 := two_pow_mod_two hp
  have hq2 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  rw [h1, mul_assoc]
  intro hd
  have h2 := (Nat.mul_dvd_mul_iff_left (pow_pos (Nat.two_pow_pos p) 2)).mp hd
  have hodd1 : Odd ((2 ^ p) ^ 2 + 1) := Nat.odd_iff.mpr (by omega)
  have hodd2 : Odd (2 ^ p - 1) := Nat.odd_iff.mpr (by omega)
  exact (Nat.not_even_iff_odd.mpr (hodd1.mul hodd2)) (even_iff_two_dvd.mpr h2)

theorem two_pow_succ_dvd_sq {p : ℕ} (hp : 1 ≤ p) : 2 ^ (p + 1) ∣ (2 ^ p) ^ 2 := by
  rw [← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem two_pow_two_mul_succ_dvd_cube {p : ℕ} (hp : 1 ≤ p) : 2 ^ (2 * p + 1) ∣ (2 ^ p) ^ 3 := by
  rw [← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem sq_dvd_suzuki (q : ℕ) : q ^ 2 ∣ q ^ 2 * (q ^ 2 + 1) * (q - 1) :=
  (dvd_mul_right _ _).mul_right _

theorem eight_dvd_two_pow {p : ℕ} (hp : 3 ≤ p) : 8 ∣ 2 ^ p := pow_dvd_pow 2 hp

theorem nine_dvd_three_pow {p : ℕ} (hp : 2 ≤ p) : 9 ∣ 3 ^ p := pow_dvd_pow 3 hp

theorem twentyseven_dvd_three_pow {p : ℕ} (hp : 3 ≤ p) : 27 ∣ 3 ^ p := pow_dvd_pow 3 hp

theorem two_pow_cube_dvd_psu3 {p : ℕ} (hp : Odd p) :
    (2 ^ p) ^ 3 ∣ (2 ^ p) ^ 3 * ((2 ^ p) ^ 3 + 1) * ((2 ^ p) ^ 2 - 1) / 3 := by
  have h3 : 3 ∣ ((2 ^ p) ^ 3 + 1) * ((2 ^ p) ^ 2 - 1) :=
    (three_dvd_cube_add_one (two_pow_mod_three hp)).mul_right _
  rw [mul_assoc, Nat.mul_div_assoc _ h3]
  exact dvd_mul_right _ _

theorem three_pow_mod_two (p : ℕ) : 3 ^ p % 2 = 1 := by
  rw [Nat.pow_mod]
  norm_num

theorem two_dvd_three_pow_sq_sub_one (p : ℕ) : 2 ∣ (3 ^ p) ^ 2 - 1 := by
  have h1 : (3 ^ p) ^ 2 % 2 = 1 := by rw [Nat.pow_mod, three_pow_mod_two]
  have h2 : 1 ≤ (3 ^ p) ^ 2 := Nat.one_le_pow _ _ (pow_pos (by norm_num) p)
  omega

theorem three_pow_dvd_psl2_three (p : ℕ) : 3 ^ p ∣ 3 ^ p * ((3 ^ p) ^ 2 - 1) / 2 := by
  rw [Nat.mul_div_assoc _ (two_dvd_three_pow_sq_sub_one p)]
  exact dvd_mul_right _ _

theorem not_eight_dvd_psl2_three {p : ℕ} (hp : Odd p) : ¬ 8 ∣ 3 ^ p * ((3 ^ p) ^ 2 - 1) / 2 := by
  intro hd
  have hmod := three_pow_sq_mod_sixteen hp
  have h1 : 1 ≤ (3 ^ p) ^ 2 := Nat.one_le_pow _ _ (pow_pos (by norm_num) p)
  rw [Nat.mul_div_assoc _ (two_dvd_three_pow_sq_sub_one p)] at hd
  have hcop : Nat.Coprime 8 (3 ^ p) := Nat.Coprime.pow_right p (by norm_num)
  have := hcop.dvd_of_dvd_mul_left hd
  omega

theorem not_twentyseven_dvd_psu3 {q : ℕ} (h : q % 9 = 2 ∨ q % 9 = 5) :
    ¬ 27 ∣ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) / 3 := by
  intro hd
  have hq3 : q % 3 = 2 := by omega
  have h3 : 3 ∣ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) := by
    rw [mul_assoc]
    exact (((three_dvd_cube_add_one hq3).mul_right _).mul_left _)
  have hcancel := Nat.mul_div_cancel' h3
  refine not_eightyone_dvd_unitary h ?_
  obtain ⟨k, hk⟩ := hd
  exact ⟨k, by omega⟩

theorem psu3_order_dvd {q : ℕ} (h : q % 3 = 2) :
    q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) / 3 ∣ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) := by
  refine Nat.div_dvd_of_dvd ?_
  rw [mul_assoc]
  exact (((three_dvd_cube_add_one h).mul_right _).mul_left _)

end CFSG.SignalizerFunctorTheorem.McBride.NearSolvable
