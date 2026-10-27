module

public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Monster.Existence

private theorem commutator_le_of_index_eq_two {G : Type*} [Group G] {K : Subgroup G}
    (hK : K.index = 2) : commutator G ≤ K := by
  have : K.Normal := Subgroup.normal_of_index_eq_two hK
  have hc : Nat.card (G ⧸ K) = 2 := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (G ⧸ K) := isCyclic_of_prime_card hc
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).1 inferInstance

theorem eq_commutator_of_index_eq_two {G : Type*} [Group G] (h2 : (commutator G).index = 2)
    {K : Subgroup G} (hK : K.index = 2) : K = commutator G := by
  have : K.FiniteIndex := ⟨by rw [hK]; norm_num⟩
  have : (commutator G).FiniteIndex := ⟨by rw [h2]; norm_num⟩
  exact (Subgroup.eq_of_index_dvd_index (commutator_le_of_index_eq_two hK)
    (by rw [h2, hK])).symm

theorem not_mem_of_relIndex_eq_two {G G' : Type*} [Group G] [Group G'] (ρ : G ≃* G')
    (H : Subgroup G) (H' : Subgroup G') (hH : ∀ x, x ∈ H ↔ ρ x ∈ H')
    (h2 : (commutator H').index = 2) {t : G} (ht : t ∈ H)
    (hout : ∀ y : H', (y : G') = ρ t → y ∉ commutator H') {K : Subgroup G}
    (hK : K.relIndex H = 2) : t ∉ K := by
  let e : H ≃* H' :=
    { toFun := fun x => ⟨ρ x.1, (hH x.1).1 x.2⟩
      invFun := fun y => ⟨ρ.symm y.1, (hH _).2 (by simp)⟩
      left_inv := fun x => Subtype.ext (ρ.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (ρ.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul ρ x.1 y.1) }
  have hK1 : ((K.subgroupOf H).map (e : H →* H')).index = 2 := by
    rw [Subgroup.index_map_equiv]
    exact hK
  have hmap : (K.subgroupOf H).map (e : H →* H') = commutator H' :=
    eq_commutator_of_index_eq_two h2 hK1
  intro htK
  have hmem : e ⟨t, ht⟩ ∈ commutator H' := by
    rw [← hmap]
    exact ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.2 htK, rfl⟩
  exact hout (e ⟨t, ht⟩) rfl hmem

end CFSG.Monster.Existence
