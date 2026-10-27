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
public import Mathlib.GroupTheory.GroupAction.MultiplePrimitivity
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

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem three_point_remaining_card
    (X : Type) [Fintype X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (t : Set X) (ht : t.ncard = 3) :
    Nat.card (SubMulAction.ofFixingSubgroup P t) = 21 := by
  change Nat.card ↥(tᶜ : Set X) = 21
  rw [Nat.card_coe_set_eq]
  have htotal := Set.ncard_add_ncard_compl t
  rw [Nat.card_eq_fintype_card, hcard, ht] at htotal
  omega

theorem three_point_stabilizer_is_preprimitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (t : Set X) (ht : t.ncard = 3) :
    MulAction.IsPreprimitive
      (fixingSubgroup P t)
      (SubMulAction.ofFixingSubgroup P t) := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  have hP4primitive :
      MulAction.IsMultiplyPreprimitive P X 4 :=
    MulAction.isMultiplyPreprimitive_of_isMultiplyPretransitive_succ
      P X (by
        rw [ENat.card_eq_coe_fintype_card, hcard]
        norm_num)
  letI : MulAction.IsMultiplyPreprimitive P X 4 :=
    hP4primitive
  apply
    MulAction.IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup
      P 4
  rw [← (Set.toFinite t).cast_ncard_eq, ht]
  norm_num

theorem three_point_stabilizer_card_eq_four_hundred_twenty_mul
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (t : Set X) (ht : t.ncard = 3) :
    Nat.card (fixingSubgroup P t) =
      420 * Nat.card (fixingSubgroup P s) := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex :
      (fixingSubgroup P s).index = 5100480 := by
    omega
  have hLindexRaw :=
    hP3.index_of_fixingSubgroup_mul ht
  rw [Nat.card_eq_fintype_card, hcard] at hLindexRaw
  norm_num at hLindexRaw
  have hLindex :
      (fixingSubgroup P t).index = 12144 := by
    omega
  have hHindexCard :=
    (fixingSubgroup P s).index_mul_card
  have hLindexCard :=
    (fixingSubgroup P t).index_mul_card
  rw [hHindex] at hHindexCard
  rw [hLindex] at hLindexCard
  omega

end FiveTransitive.Degree24

end CFSG
