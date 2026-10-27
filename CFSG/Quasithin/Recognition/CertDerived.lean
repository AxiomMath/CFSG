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

open scoped commutatorElement

namespace CFSG.Quasithin

theorem mem_normalizer_of_involution {G : Type*} [Group G] {T : Set G} {s : G} (hs : s * s = 1)
    (h : ∀ t ∈ T, s * t * s⁻¹ ∈ Subgroup.closure T) :
    s ∈ Subgroup.normalizer (Subgroup.closure T : Set G) := by
  have hmap : ∀ x ∈ Subgroup.closure T, s * x * s⁻¹ ∈ Subgroup.closure T := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => simp
    | mul x y _ _ hx hy =>
      have : s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hmap x hx, fun hx => ?_⟩
  have h2 := hmap _ hx
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have e : s * (s * x * s⁻¹) * s⁻¹ = x := by
    rw [hs']
    calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
      _ = x := by rw [hs]; group
  rwa [e] at h2

theorem commutator_closure_le_of_involutions {G : Type*} [Group G] {S T : Set G}
    (hS : ∀ s ∈ S, s * s = 1) (hconj : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ Subgroup.closure T)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ Subgroup.closure T) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ ≤ Subgroup.closure T := by
  set U := Subgroup.closure T with hU
  have hnorm : Subgroup.closure S ≤ Subgroup.normalizer (U : Set G) := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    exact mem_normalizer_of_involution (hS s hs) (hconj s hs)
  have hconjU : ∀ x ∈ Subgroup.closure S, ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.1 (hnorm hx) u).1 hu
  rw [Subgroup.commutator_le]
  intro x hx y hy
  induction hx, hy using Subgroup.closure_induction₂ with
  | mem x y hx hy => exact hcomm x hx y hy
  | one_left y hy => simp
  | one_right x hx => simp
  | mul_left x₁ x₂ y hx₁ hx₂ hy h₁ h₂ =>
    have e : ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact U.mul_mem (hconjU x₁ hx₁ _ h₂) h₁
  | mul_right y₁ y₂ x hy₁ hy₂ hx h₁ h₂ =>
    have e : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact U.mul_mem h₁ (hconjU y₁ hy₁ _ h₂)
  | inv_left x y hx hy h =>
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hxi : x⁻¹ ∈ Subgroup.closure S := Subgroup.inv_mem _ hx
    have := hconjU x⁻¹ hxi _ (U.inv_mem h)
    simpa using this
  | inv_right x y hx hy h =>
    have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hyi : y⁻¹ ∈ Subgroup.closure S := Subgroup.inv_mem _ hy
    have := hconjU y⁻¹ hyi _ (U.inv_mem h)
    simpa using this

end CFSG.Quasithin
