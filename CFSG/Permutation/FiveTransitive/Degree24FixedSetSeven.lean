module

public import CFSG.Permutation.FiveTransitive.Degree24ThirteenFiniteChecks
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

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

@[expose] noncomputable def fiveEmbeddingOfSet
    (X : Type) [Fintype X]
    (t : Set X) (ht : t.ncard = 5) :
    Fin 5 ↪ X := by
  letI : Fintype t := Fintype.ofFinite t
  have htCard : Fintype.card t = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, ht]
  let et : t ≃ Fin 5 :=
    Fintype.equivFinOfCardEq htCard
  exact {
    toFun := fun i => (et.symm i).1
    inj' := by
      intro i j hij
      apply et.symm.injective
      exact Subtype.ext hij }

theorem range_fiveEmbeddingOfSet
    (X : Type) [Fintype X]
    (t : Set X) (ht : t.ncard = 5) :
    Set.range (fiveEmbeddingOfSet X t ht) = t := by
  classical
  letI : Fintype t := Fintype.ofFinite t
  have htCard : Fintype.card t = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, ht]
  let et : t ≃ Fin 5 :=
    Fintype.equivFinOfCardEq htCard
  change
    Set.range
      (fun i => ((et.symm i : t) : X)) = t
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (et.symm i).2
  · intro hx
    obtain ⟨i, hi⟩ :=
      et.symm.surjective ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩

end FiveTransitive.Degree24

end CFSG
