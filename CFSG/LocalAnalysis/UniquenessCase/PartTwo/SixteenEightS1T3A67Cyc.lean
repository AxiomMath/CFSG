module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16t3_cycleType_of_isPGroup_three {n : ℕ} (hn : n ≤ 8) (σ : Equiv.Perm (Fin n))
    (hσ : IsPGroup 3 (Subgroup.zpowers σ)) :
    σ.cycleType = 0 ∨ σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ :=
    hσ.exists_orderOf_eq_pow (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ)
  have horder : orderOf σ = 3 ^ k := by
    rw [← Subgroup.orderOf_mk σ (Subgroup.mem_zpowers σ)]
    exact hk
  have hmem : ∀ m ∈ σ.cycleType, m = 3 := by
    intro m hm
    have hdvd : m ∣ 3 ^ k := by
      rw [← horder]
      exact Equiv.Perm.dvd_of_mem_cycleType hm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdvd
    have h2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
    have h8 : m ≤ 8 := by
      have hle := Multiset.le_sum_of_mem hm
      rw [Equiv.Perm.sum_cycleType] at hle
      exact hle.trans ((Finset.card_le_univ σ.support).trans (by simpa using hn))
    have hjle : j ≤ 1 := by
      by_contra h
      have h2j : 2 ≤ j := by omega
      have hpow : 3 ^ 2 ≤ 3 ^ j := pow_le_pow_right' (by norm_num) h2j
      norm_num at hpow
      omega
    have hjge : 1 ≤ j := by
      by_contra h
      have hj0 : j = 0 := by omega
      rw [hj0] at hj
      norm_num at hj
      omega
    have hj1 : j = 1 := by omega
    rw [hj1] at hj
    norm_num at hj
    exact hj
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate_of_mem hmem
  have hle : Multiset.card σ.cycleType * 3 ≤ 8 := by
    have hsum : σ.cycleType.sum = Multiset.card σ.cycleType * 3 := by
      conv_lhs => rw [hrep]
      rw [Multiset.sum_replicate]
      exact Nat.nsmul_eq_mul _ _
    rw [← hsum, Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ σ.support).trans (by simpa using hn)
  have hc2 : Multiset.card σ.cycleType ≤ 2 := by omega
  set c := Multiset.card σ.cycleType with hc
  interval_cases c
  · left; simpa using hrep
  · right; left; simpa using hrep
  · right; right; simpa using hrep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
