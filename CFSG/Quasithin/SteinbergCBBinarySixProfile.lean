module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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

namespace CFSG.Quasithin.SteinbergCB

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def linFix (B : Subgroup (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V :=
  ⨅ g ∈ B, LinearMap.ker ((g : V →ₗ[ZMod 2] V) - LinearMap.id)

@[expose] def linComm (B : Subgroup (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ g ∈ B, ∃ v : V, w = g v - v}

@[expose] noncomputable def linRank (g : V ≃ₗ[ZMod 2] V) : ℕ :=
  finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id))

@[expose] def QTBinarySixProfile (b : LinearMap.BilinForm (ZMod 2) V)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  finrank (ZMod 2) V = 6 ∧ b.Nondegenerate ∧ b.IsAlt ∧
    (∀ g ∈ Γ, ∀ x y : V, b (g x) (g y) = b x y) ∧
    (∀ e ∈ Γ, orderOf e = 2 → 2 ≤ linRank e) ∧
    ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ Γ → E ≠ ⊥ → CFSG.IsElementaryAbelian 2 E →
      (∀ B : Subgroup (V ≃ₗ[ZMod 2] V), B ≤ E → B.relIndex E = 2 → linFix B = linFix E) →
      Nat.card E = 8 ∧ linFix E = linComm E ∧ finrank (ZMod 2) (linFix E) = 3 ∧
        ∃ e ∈ E, e ≠ 1 ∧ linRank e = 2

end CFSG.Quasithin.SteinbergCB
