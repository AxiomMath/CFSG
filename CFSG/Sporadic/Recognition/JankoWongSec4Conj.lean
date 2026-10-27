module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.Sporadic.Recognition.JankoWong

variable {G : Type*} [Group G]

@[expose] def cj (x y : G) : G := y⁻¹ * x * y

theorem cj_def (x y : G) : cj x y = y⁻¹ * x * y := rfl

@[simp] theorem cj_one_left (y : G) : cj (1 : G) y = 1 := by simp [cj]

@[simp] theorem cj_one_right (x : G) : cj x (1 : G) = x := by simp [cj]

theorem cj_mul_left (x x' y : G) : cj (x * x') y = cj x y * cj x' y := by
  simp [cj, mul_assoc]

theorem cj_inv_left (x y : G) : cj x⁻¹ y = (cj x y)⁻¹ := by simp [cj, mul_assoc]

theorem cj_pow_left (x y : G) (n : ℕ) : cj (x ^ n) y = cj x y ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, cj_mul_left, ih, pow_succ]

theorem cj_zpow_left (x y : G) (n : ℤ) : cj (x ^ n) y = cj x y ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using cj_pow_left x y m
  · rw [zpow_neg, cj_inv_left, zpow_neg]; simpa using congrArg (·⁻¹) (cj_pow_left x y m)

theorem cj_cj (x y w : G) : cj (cj x y) w = cj x (y * w) := by simp [cj, mul_assoc]

theorem cj_mul_right (x y w : G) : cj x (y * w) = cj (cj x y) w := (cj_cj x y w).symm

theorem cj_inv_right (x y : G) : cj x y⁻¹ = y * x * y⁻¹ := by simp [cj]

theorem cj_cj_inv (x y : G) : cj (cj x y) y⁻¹ = x := by simp [cj, mul_assoc]

theorem cj_inv_cj (x y : G) : cj (cj x y⁻¹) y = x := by simp [cj, mul_assoc]

theorem cj_eq_self_of_comm {x y : G} (h : x * y = y * x) : cj x y = x := by
  unfold cj; rw [mul_assoc, h]; simp

theorem comm_of_cj_eq {x y : G} (h : cj x y = x) : x * y = y * x := by
  unfold cj at h
  calc x * y = y * (y⁻¹ * x * y) := by group
    _ = y * x := by rw [h]

theorem cj_eq_iff_comm {x y : G} : cj x y = x ↔ x * y = y * x :=
  ⟨comm_of_cj_eq, cj_eq_self_of_comm⟩

theorem cj_injective_left (y : G) : Function.Injective fun x : G => cj x y := by
  intro x x' h
  simpa [cj] using h

theorem cj_eq_iff_eq_cj_inv {x y w : G} : cj x y = w ↔ x = cj w y⁻¹ := by
  constructor
  · rintro rfl; simp [cj, mul_assoc]
  · rintro rfl; simp [cj, mul_assoc]

theorem cj_comm (x y w : G) :
    cj (x⁻¹ * y⁻¹ * x * y) w = (cj x w)⁻¹ * (cj y w)⁻¹ * cj x w * cj y w := by
  simp [cj, mul_assoc]

end CFSG.Sporadic.Recognition.JankoWong
