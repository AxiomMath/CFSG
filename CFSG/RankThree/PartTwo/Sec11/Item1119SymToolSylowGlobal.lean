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
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_SylowGlobal_mem_normalizer {G : Type*} [Group G]
    (P Q : Subgroup G) (hPQ : P ≤ Q) (q : Q)
    (hq : q ∈ Subgroup.normalizer ((P.subgroupOf Q : Subgroup Q) : Set Q)) :
    (q : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have hgQ : g ∈ Q := hPQ hg
    have hn : (⟨g, hgQ⟩ : Q) ∈ P.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hg
    have hc := (Subgroup.mem_normalizer_iff.mp hq ⟨g, hgQ⟩).mp hn
    have hc' := Subgroup.mem_subgroupOf.mp hc
    simpa using hc'
  · intro hc
    have hqQ : (q : G) ∈ Q := q.2
    have hgQ : g ∈ Q := by
      have key : (q : G)⁻¹ * ((q : G) * g * (q : G)⁻¹) * (q : G) = g := by group
      have hmem : (q : G)⁻¹ * ((q : G) * g * (q : G)⁻¹) * (q : G) ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem hqQ) (hPQ hc)) hqQ
      rwa [key] at hmem
    have hconjH : q * (⟨g, hgQ⟩ : Q) * q⁻¹ ∈ P.subgroupOf Q := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hc
    have hn : (⟨g, hgQ⟩ : Q) ∈ P.subgroupOf Q :=
      (Subgroup.mem_normalizer_iff.mp hq ⟨g, hgQ⟩).mpr hconjH
    exact Subgroup.mem_subgroupOf.mp hn

theorem not_dvd_index_of_normalizer_maximal {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (hP : IsPGroup 3 P)
    (h : ∀ S : Subgroup G, IsPGroup 3 S → P ≤ S → S ≤ Subgroup.normalizer (P : Set G) → S = P) :
    ¬ 3 ∣ P.index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hQ3 : IsPGroup 3 (Q : Subgroup G) := Q.isPGroup'
  have hPR : P = (Q : Subgroup G) := by
    by_contra hne
    have hlt : P < (Q : Subgroup G) := lt_of_le_of_ne hPQ hne
    haveI : Group.IsNilpotent (Q : Subgroup G) := hQ3.isNilpotent
    have hnc : NormalizerCondition (Q : Subgroup G) :=
      Group.normalizerCondition_of_isNilpotent
    have hHtop : P.subgroupOf (Q : Subgroup G) < ⊤ := by
      obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt hlt
      refine lt_top_iff_ne_top.mpr fun hTop => hxP ?_
      have hmem : (⟨x, hxQ⟩ : (Q : Subgroup G)) ∈ P.subgroupOf (Q : Subgroup G) := by
        rw [hTop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    obtain ⟨q, hqN, hqH⟩ := SetLike.exists_of_lt (hnc _ hHtop)
    have hqP : (q : G) ∈ Subgroup.normalizer (P : Set G) :=
      aux_SylowGlobal_mem_normalizer P (Q : Subgroup G) hPQ q hqN
    have hqQ : (q : G) ∈ (Q : Subgroup G) := q.2
    obtain ⟨S, hS⟩ : ∃ S : Subgroup G,
        S = Subgroup.normalizer (P : Set G) ⊓ (Q : Subgroup G) := ⟨_, rfl⟩
    have hSQ : S ≤ (Q : Subgroup G) := by
      rw [hS]
      exact inf_le_right
    have hSN : S ≤ Subgroup.normalizer (P : Set G) := by
      rw [hS]
      exact inf_le_left
    have hPS : P ≤ S := by
      rw [hS]
      exact le_inf Subgroup.le_normalizer hPQ
    have hS3 : IsPGroup 3 S := hQ3.to_le hSQ
    have hSP : S = P := h S hS3 hPS hSN
    have hqS : (q : G) ∈ S := by
      rw [hS]
      exact Subgroup.mem_inf.mpr ⟨hqP, hqQ⟩
    rw [hSP] at hqS
    exact hqH (Subgroup.mem_subgroupOf.mpr hqS)
  rw [hPR]
  exact Sylow.not_dvd_index Q

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
