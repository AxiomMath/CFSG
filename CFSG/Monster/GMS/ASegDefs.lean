module

public import CFSG.Monster.GMS.Graph
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

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def CentInvAutInnerAt (x t : G) : Prop :=
  ∀ ψ : ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t}) ≃*
      ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t}),
    (∀ g : ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t}),
      (g : G) = x → ψ g = g) →
    (∀ g : ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t}),
      (g : G) = t → ψ g = g) →
      ∃ h ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t},
        ∀ g : ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t}),
          (ψ g : G) = h * g * h⁻¹

@[expose] def CentInvAutInnerTwoA (a : G) : Prop :=
  ∀ x t : G, IsConj a x → t ∈ twoANbr a x → CentInvAutInnerAt x t

@[expose] def CentInvAutInnerTwoAB (a z₀ : G) : Prop :=
  ∀ x t : G, IsConj a x → t ∈ twoABNbr a z₀ x → CentInvAutInnerAt x t

theorem orderOf_eq_two_of_isConj' {a x : G} (ha : orderOf a = 2) (hx : IsConj a x) :
    orderOf x = 2 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  rw [← ha]
  exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a

theorem mul_self_eq_one_of_orderOf_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← sq, ← hx, pow_orderOf_eq_one]

theorem mul_comm_of_mul_self {x t : G} (hx : x * x = 1) (ht : t * t = 1)
    (hxt : x * t * (x * t) = 1) : t * x = x * t :=
  calc t * x = (x * x) * t * x * (t * t) := by rw [hx, ht]; group
    _ = x * (x * t * (x * t)) * t := by group
    _ = x * t := by rw [hxt]; group

end CFSG.Monster.GMS
