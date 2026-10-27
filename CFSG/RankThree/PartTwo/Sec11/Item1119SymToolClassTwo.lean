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

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem comm_zpow_zpow {G : Type*} [Group G] (u v k : G)
    (hk : u * v * u⁻¹ * v⁻¹ = k) (hku : u * k = k * u) (hkv : v * k = k * v) (i j : ℤ) :
    u ^ i * v ^ j * (u ^ i)⁻¹ * (v ^ j)⁻¹ = k ^ (i * j) := by
  have hCu : Commute u k := hku
  have hCv : Commute v k := hkv
  have huv : u * v = k * (v * u) := by
    rw [← hk]
    group
  have hvu : v * u = k⁻¹ * (u * v) := by
    rw [huv, inv_mul_cancel_left]
  have hconj : u * v * u⁻¹ = k * v := by
    rw [← hk, inv_mul_cancel_right]
  have hconj' : u⁻¹ * v * u = k⁻¹ * v := by
    have hc : u⁻¹ * k⁻¹ = k⁻¹ * u⁻¹ := hCu.inv_inv.eq
    calc u⁻¹ * v * u = u⁻¹ * (v * u) := mul_assoc _ _ _
      _ = u⁻¹ * (k⁻¹ * (u * v)) := by rw [hvu]
      _ = (u⁻¹ * k⁻¹) * (u * v) := (mul_assoc _ _ _).symm
      _ = (k⁻¹ * u⁻¹) * (u * v) := by rw [hc]
      _ = k⁻¹ * (u⁻¹ * (u * v)) := mul_assoc _ _ _
      _ = k⁻¹ * v := by rw [inv_mul_cancel_left]
  have hcm : ∀ m : ℤ, u ^ m * k = k * u ^ m := fun m => (hCu.zpow_left m).eq
  have hcm' : ∀ m : ℤ, u ^ m * k⁻¹ = k⁻¹ * u ^ m :=
    fun m => (hCu.zpow_left m).inv_right.eq
  have hkk : ∀ m : ℤ, k⁻¹ * k ^ m = k ^ m * k⁻¹ :=
    fun m => (Commute.self_zpow k m).inv_left.eq
  have hstepUp : ∀ m : ℤ, u ^ m * v * (u ^ m)⁻¹ = k ^ m * v →
      u ^ (m + 1) * v * (u ^ (m + 1))⁻¹ = k ^ (m + 1) * v := by
    intro m ih
    rw [zpow_add_one u m, zpow_add_one k m, mul_inv_rev]
    calc u ^ m * u * v * (u⁻¹ * (u ^ m)⁻¹)
        = u ^ m * (u * v * u⁻¹) * (u ^ m)⁻¹ := by simp only [mul_assoc]
      _ = u ^ m * (k * v) * (u ^ m)⁻¹ := by rw [hconj]
      _ = (u ^ m * k) * v * (u ^ m)⁻¹ := by simp only [mul_assoc]
      _ = (k * u ^ m) * v * (u ^ m)⁻¹ := by rw [hcm m]
      _ = k * (u ^ m * v * (u ^ m)⁻¹) := by simp only [mul_assoc]
      _ = k * (k ^ m * v) := by rw [ih]
      _ = k ^ m * k * v := by rw [← mul_assoc, (Commute.self_zpow k m).eq]
  have hstepDown : ∀ m : ℤ, u ^ m * v * (u ^ m)⁻¹ = k ^ m * v →
      u ^ (m - 1) * v * (u ^ (m - 1))⁻¹ = k ^ (m - 1) * v := by
    intro m ih
    rw [zpow_sub_one u m, zpow_sub_one k m, mul_inv_rev, inv_inv]
    calc u ^ m * u⁻¹ * v * (u * (u ^ m)⁻¹)
        = u ^ m * (u⁻¹ * v * u) * (u ^ m)⁻¹ := by simp only [mul_assoc]
      _ = u ^ m * (k⁻¹ * v) * (u ^ m)⁻¹ := by rw [hconj']
      _ = (u ^ m * k⁻¹) * v * (u ^ m)⁻¹ := by simp only [mul_assoc]
      _ = (k⁻¹ * u ^ m) * v * (u ^ m)⁻¹ := by rw [hcm' m]
      _ = k⁻¹ * (u ^ m * v * (u ^ m)⁻¹) := by simp only [mul_assoc]
      _ = k⁻¹ * (k ^ m * v) := by rw [ih]
      _ = k ^ m * k⁻¹ * v := by rw [← mul_assoc, hkk m]
  have hQ : ∀ m : ℤ, u ^ m * v * (u ^ m)⁻¹ = k ^ m * v := by
    intro m
    induction m with
    | zero => simp
    | succ n ih => exact hstepUp _ ih
    | pred n ih => exact hstepDown _ ih
  have hF : u ^ i * v ^ j * (u ^ i)⁻¹ = k ^ (i * j) * v ^ j := by
    rw [← conj_zpow, hQ i, (hCv.symm.zpow_left i).mul_zpow j, ← zpow_mul]
  rw [hF, mul_inv_cancel_right]

theorem pow_three_of_comm_central {G : Type*} [Group G] (u v k : G)
    (hk : u * v * u⁻¹ * v⁻¹ = k) (hku : u * k = k * u) (hkv : v * k = k * v)
    (hk3 : k ^ 3 = 1) : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  have hCu : Commute u k := hku
  have hCv : Commute v k := hkv
  have huv : u * v = k * (v * u) := by
    rw [← hk]
    group
  have hvu : v * u = k⁻¹ * (u * v) := by
    rw [huv, inv_mul_cancel_left]
  have hcu : u * k⁻¹ = k⁻¹ * u := hCu.inv_right.eq
  have hcv : v * k⁻¹ = k⁻¹ * v := hCv.inv_right.eq
  have hk3' : k⁻¹ * k⁻¹ * k⁻¹ = 1 := by
    have h : k * (k * k) = 1 := (pow_three k).symm.trans hk3
    calc k⁻¹ * k⁻¹ * k⁻¹ = (k * (k * k))⁻¹ := by group
      _ = 1 := by rw [h, inv_one]
  have ha : ∀ X : G, u * (k⁻¹ * X) = k⁻¹ * (u * X) := fun X => by
    calc u * (k⁻¹ * X) = (u * k⁻¹) * X := (mul_assoc _ _ _).symm
      _ = (k⁻¹ * u) * X := by rw [hcu]
      _ = k⁻¹ * (u * X) := mul_assoc _ _ _
  have hb : ∀ X : G, v * (k⁻¹ * X) = k⁻¹ * (v * X) := fun X => by
    calc v * (k⁻¹ * X) = (v * k⁻¹) * X := (mul_assoc _ _ _).symm
      _ = (k⁻¹ * v) * X := by rw [hcv]
      _ = k⁻¹ * (v * X) := mul_assoc _ _ _
  have hc : ∀ X : G, v * (u * X) = k⁻¹ * (u * (v * X)) := fun X => by
    calc v * (u * X) = (v * u) * X := (mul_assoc _ _ _).symm
      _ = (k⁻¹ * (u * v)) * X := by rw [hvu]
      _ = k⁻¹ * ((u * v) * X) := mul_assoc _ _ _
      _ = k⁻¹ * (u * (v * X)) := by rw [mul_assoc u v X]
  have hd : ∀ X : G, k⁻¹ * (k⁻¹ * (k⁻¹ * X)) = X := fun X => by
    calc k⁻¹ * (k⁻¹ * (k⁻¹ * X)) = (k⁻¹ * k⁻¹ * k⁻¹) * X := by simp only [mul_assoc]
      _ = X := by rw [hk3', one_mul]
  simp only [pow_three, mul_assoc, ha, hb, hc, hd]

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
