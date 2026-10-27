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

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem mutually_normalizing_abelian_intersection_central
    (first second : Subgroup GroupType)
    (first_abelian : IsMulCommutative first) (second_abelian : IsMulCommutative second) :
    first ⊓ second ≤ Subgroup.centralizer ((first ⊔ second : Subgroup GroupType) : Set GroupType) := by
  let := first_abelian
  let := second_abelian
  apply Subgroup.le_centralizer_iff.mpr
  apply sup_le
  · exact (Subgroup.le_centralizer first).trans (Subgroup.centralizer_le inf_le_left)
  · exact (Subgroup.le_centralizer second).trans (Subgroup.centralizer_le inf_le_right)

theorem mutually_normalizing_abelian_product_derived
    (first second : Subgroup GroupType)
    (first_abelian : IsMulCommutative first) (second_abelian : IsMulCommutative second)
    (first_normalizes : first ≤ Subgroup.normalizer (second : Set GroupType))
    (second_normalizes : second ≤ Subgroup.normalizer (first : Set GroupType)) :
    ⁅first ⊔ second, first ⊔ second⁆ ≤ first ⊓ second := by
  let := first_abelian
  let := second_abelian
  let parent := first ⊔ second
  let internalFirst := first.subgroupOf parent
  let internalSecond := second.subgroupOf parent
  have first_le : first ≤ parent := le_sup_left
  have second_le : second ≤ parent := le_sup_right
  let _firstNormal : internalFirst.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer first_le).mpr
    (sup_le Subgroup.le_normalizer second_normalizes)
  let _secondNormal : internalSecond.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer second_le).mpr
    (sup_le first_normalizes Subgroup.le_normalizer)
  have whole : internalFirst ⊔ internalSecond = ⊤ := by
    apply Subgroup.map_injective parent.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le first_le,
      Subgroup.map_subgroupOf_eq_of_le second_le, ← MonoidHom.range_eq_map, parent.subtype_range]
  have derived_le_first : commutator parent ≤ internalFirst :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top whole inferInstance
  have derived_le_second : commutator parent ≤ internalSecond :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      ((sup_comm internalSecond internalFirst).trans whole) inferInstance
  have first_bound := Subgroup.map_mono (f := parent.subtype) derived_le_first
  have second_bound := Subgroup.map_mono (f := parent.subtype) derived_le_second
  rw [map_commutator_eq, parent.subtype_range, Subgroup.map_subgroupOf_eq_of_le first_le] at first_bound
  rw [map_commutator_eq, parent.subtype_range, Subgroup.map_subgroupOf_eq_of_le second_le] at second_bound
  exact le_inf first_bound second_bound

theorem mutually_normalizing_abelian_product_class_two
    (first second : Subgroup GroupType)
    (first_abelian : IsMulCommutative first) (second_abelian : IsMulCommutative second)
    (first_normalizes : first ≤ Subgroup.normalizer (second : Set GroupType))
    (second_normalizes : second ≤ Subgroup.normalizer (first : Set GroupType)) :
    ⁅first ⊔ second, first ⊔ second⁆ ≤
      Subgroup.centralizer ((first ⊔ second : Subgroup GroupType) : Set GroupType) :=
  (mutually_normalizing_abelian_product_derived first second first_abelian second_abelian
    first_normalizes second_normalizes).trans
      (mutually_normalizing_abelian_intersection_central first second first_abelian second_abelian)

end CFSG.SignalizerFunctor.Helpers
