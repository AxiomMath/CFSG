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

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

variable {G : Type*} [Group G]

theorem commutator_commutator_le_of_rotate {N H₁ H₂ H₃ : Subgroup G} [N.Normal]
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have key : ∀ K : Subgroup G, K ≤ N ↔ K.map (QuotientGroup.mk' N) = ⊥ := fun K => by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  simp only [map_commutator] at h1 h2 ⊢
  exact commutator_commutator_eq_bot_of_rotate h1 h2

theorem perfect_abelian_action_commutator {X A : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hA : IsMulCommutative A) (hXA : X ≤ normalizer (A : Set G)) :
    ⁅⁅A, X⁆, X⁆ = ⁅A, X⁆ := by
  set W := ⁅A, X⁆ with hW
  set U := ⁅W, X⁆ with hU
  have hWA : W ≤ A := by
    rw [hW, commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp hXA
  have hUW : U ≤ W := by
    rw [hU, commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp (normalizer_commutator_ge_right A X)
  refine le_antisymm hUW ?_
  set K := normalizer (U : Set G) with hK
  have hAK : A ≤ K := by
    refine le_trans (fun a ha => ?_) (centralizer_le_normalizer (U : Set G))
    rw [mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (hA.is_comm.comm ⟨u, hWA (hUW hu)⟩ ⟨a, ha⟩)
  have hXK : X ≤ K := normalizer_commutator_ge_right W X
  have hUK : U ≤ K := le_normalizer
  have hinj := K.subtype_injective
  have hmA := map_subgroupOf_eq_of_le hAK
  have hmX := map_subgroupOf_eq_of_le hXK
  have hmU := map_subgroupOf_eq_of_le hUK
  have : (U.subgroupOf K).Normal := normal_in_normalizer
  have h1 : ⁅⁅X.subgroupOf K, A.subgroupOf K⁆, X.subgroupOf K⁆ ≤ U.subgroupOf K := by
    rw [← map_le_map_iff_of_injective hinj, map_commutator, map_commutator, hmA, hmX, hmU,
      commutator_comm X A]
  have h2 : ⁅⁅A.subgroupOf K, X.subgroupOf K⁆, X.subgroupOf K⁆ ≤ U.subgroupOf K := by
    rw [← map_le_map_iff_of_injective hinj, map_commutator, map_commutator, hmA, hmX, hmU]
  have h3 := commutator_commutator_le_of_rotate h1 h2
  have hX' : ⁅X.subgroupOf K, X.subgroupOf K⁆ = X.subgroupOf K := by
    apply map_injective hinj
    rw [map_commutator, hmX, hX]
  rw [hX', ← map_le_map_iff_of_injective hinj, map_commutator, hmA, hmX, hmU] at h3
  rw [hW, commutator_comm]
  exact h3

end CFSG.Quasithin.SteinbergBM
