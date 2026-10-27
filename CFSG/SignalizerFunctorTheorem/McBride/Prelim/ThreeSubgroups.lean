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

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem three_subgroups_lemma {X Y Z : Subgroup G} (h1 : ⁅⁅X, Y⁆, Z⁆ = ⊥) (h2 : ⁅⁅Y, Z⁆, X⁆ = ⊥) :
    ⁅⁅Z, X⁆, Y⁆ = ⊥ :=
  Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem three_subgroups_lemma_normal {X Y Z N : Subgroup G} [N.Normal] (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N)
    (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) : ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  have key : ∀ A B C : Subgroup G, ⁅⁅A, B⁆, C⁆ ≤ N ↔
      ⁅⁅A.map (QuotientGroup.mk' N), B.map (QuotientGroup.mk' N)⁆,
        C.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    intro A B C
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  exact three_subgroups_lemma h1 h2

end CFSG.SignalizerFunctorTheorem.McBride
