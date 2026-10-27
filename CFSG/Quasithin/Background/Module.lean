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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def fixV (X : Subgroup (MulAut V)) : Subgroup V where
  carrier := {v | ∀ x ∈ X, x v = v}
  one_mem' := fun x _ => map_one x
  mul_mem' := fun ha hb x hx => by rw [map_mul, ha x hx, hb x hx]
  inv_mem' := fun ha x hx => by rw [map_inv, ha x hx]

theorem mem_fixV {X : Subgroup (MulAut V)} {v : V} : v ∈ fixV X ↔ ∀ x ∈ X, x v = v := Iff.rfl

@[expose] def commV (X : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {w | ∃ x ∈ X, ∃ v : V, x v * v⁻¹ = w}

@[expose] def IsElemAbelian2 (A : Subgroup (MulAut V)) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 2 = 1

@[expose] def IsQuadratic (A : Subgroup (MulAut V)) : Prop := commV A ≤ fixV A

@[expose] def IsFFStarOffender (X A : Subgroup (MulAut V)) : Prop :=
  A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    ∀ B : Subgroup (MulAut V), B ≤ A →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card A * Nat.card (fixV A)

@[expose] def IsFFModule (X : Subgroup (MulAut V)) : Prop :=
  ∃ A : Subgroup (MulAut V), A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    Nat.card V ≤ Nat.card A * Nat.card (fixV A)

@[expose] def IsStrongFFModule (X : Subgroup (MulAut V)) : Prop :=
  ∃ A : Subgroup (MulAut V), A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    Nat.card V < Nat.card A * Nat.card (fixV A)

@[expose] def ffJ (X : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ (A : Subgroup (MulAut V)) (_ : IsFFStarOffender X A), A

end CFSG.Quasithin
