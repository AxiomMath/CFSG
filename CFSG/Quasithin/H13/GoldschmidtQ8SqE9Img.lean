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

namespace CFSG.Quasithin.H13.Q8SqE9

open Subgroup

variable {G : Type*} [Group G]

theorem card_eq_card_image_mul (H K : Subgroup G) (hKH : K ≤ H) (N : Subgroup H) [N.Normal] :
    Nat.card K = Nat.card ↥((K.subgroupOf H).map (QuotientGroup.mk' N)) *
      Nat.card ↥(K ⊓ N.map H.subtype) := by
  set K' := K.subgroupOf H with hK'
  have h1 := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' N).domRestrict K')
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk'] at h1
  have hK : Nat.card K' = Nat.card K := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have h2 : Nat.card (N.subgroupOf K') = Nat.card ↥(K' ⊓ N) := by
    rw [← Subgroup.inf_subgroupOf_left N K']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : Nat.card ↥(K' ⊓ N) = Nat.card ↥(K ⊓ N.map H.subtype) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKH, ← Subgroup.map_inf _ _ _ H.subtype_injective]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  rw [← hK, ← h1, h2, h3, mul_comm]

end CFSG.Quasithin.H13.Q8SqE9
