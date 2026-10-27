module

import CFSG.Mathlib.GroupTheory.PermCommute
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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.AS91

theorem perm3_derivedSeries_two {α : Type*} [Fintype α] [DecidableEq α]
    (h : Fintype.card α = 3) : derivedSeries (Equiv.Perm α) 2 = ⊥ := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hcardA : Nat.card (alternatingGroup α) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, h]
    rfl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (alternatingGroup α) := isCyclic_of_prime_card hcardA
  haveI : IsMulCommutative (alternatingGroup α) := IsCyclic.commutative
  have hD1 : derivedSeries (Equiv.Perm α) 1 ≤ alternatingGroup α := by
    rw [derivedSeries_one]
    exact Abelianization.commutator_subset_ker (f := Equiv.Perm.sign)
  have key : ∀ a ∈ derivedSeries (Equiv.Perm α) 1, ∀ b ∈ derivedSeries (Equiv.Perm α) 1,
      a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨a, hD1 ha⟩ : alternatingGroup α) ⟨b, hD1 hb⟩)
  show derivedSeries (Equiv.Perm α) (1 + 1) = ⊥
  rw [derivedSeries_succ, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (key y hy x hx)

theorem perm3_eq_bot_of_normal_pGroup {α : Type*} [Fintype α] [DecidableEq α]
    (h : Fintype.card α = 3) (N : Subgroup (Equiv.Perm α)) [N.Normal] (hN : IsPGroup 2 N) :
    N = ⊥ := by
  have hcardP : Nat.card (Equiv.Perm α) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h]
    rfl
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hN
  have hdvd : 2 ^ k ∣ 6 := by
    rw [← hk, ← hcardP]
    exact Subgroup.card_subgroup_dvd_card N
  have hk1 : k ≤ 1 := by
    by_contra hc
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h46 : 2 ^ 2 ∣ 6 := dvd_trans h4 hdvd
    norm_num at h46
  by_contra hne
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    exact hne ((Subgroup.eq_bot_iff_forall N).2
      (fun m hm => Classical.byContradiction fun hm1 => hcon ⟨m, hm, hm1⟩))
  haveI : Nontrivial N := ⟨⟨⟨n, hnN⟩, 1, fun h' => hn1 (congrArg Subtype.val h')⟩⟩
  have hgt : 1 < Nat.card N := Finite.one_lt_card
  have hcard2 : Nat.card N = 2 := by
    interval_cases k
    · rw [pow_zero] at hk
      omega
    · rw [pow_one] at hk
      exact hk
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.1 hcard2
  have hz : ∀ z : N, z = x ∨ z = y := fun z => by
    have := Set.ext_iff.1 huniv z
    simpa using this
  have two : ∀ a b : N, a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb
    rcases hz a with ha' | ha' <;> rcases hz b with hb' | hb' <;>
      rcases hz 1 with h1 | h1 <;>
      first
      | exact ha'.trans hb'.symm
      | exact absurd (ha'.trans h1.symm) ha
      | exact absurd (hb'.trans h1.symm) hb
  have hcent : ∀ g : Equiv.Perm α, g * n * g⁻¹ = n := by
    intro g
    have hmem : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hnN g
    have hne1 : g * n * g⁻¹ ≠ 1 := by
      intro h'
      apply hn1
      simpa using h'
    have heq := two ⟨g * n * g⁻¹, hmem⟩ ⟨n, hnN⟩
      (fun h' => hne1 (congrArg Subtype.val h')) (fun h' => hn1 (congrArg Subtype.val h'))
    exact congrArg Subtype.val heq
  have hcent' : ∀ g : Equiv.Perm α, n * g = g * n := fun g =>
    (mul_inv_eq_iff_eq_mul.1 (hcent g)).symm
  exact hn1 (CFSG.perm_eq_one_of_forall_commute (by simp [Nat.card_eq_fintype_card, h]) hcent')

end CFSG.Quasithin.H13.AS91
