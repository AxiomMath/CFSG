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
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.Sporadic.HN.Local

open Equiv Equiv.Perm

theorem involution_cycleType {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : σ ^ 2 = 1) : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
  rw [Multiset.eq_replicate]
  refine ⟨rfl, fun n hn => ?_⟩
  have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have h3 : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
  have h4 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have := Nat.le_of_dvd two_pos (h3.trans h4)
  omega

theorem sign_involution {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} (h : σ ^ 2 = 1) :
    sign σ = (-1) ^ Multiset.card σ.cycleType := by
  rw [Equiv.Perm.sign_of_cycleType, involution_cycleType h]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  rw [show Multiset.card σ.cycleType * 2 + Multiset.card σ.cycleType =
    2 * Multiset.card σ.cycleType + Multiset.card σ.cycleType by ring, pow_add, pow_mul]
  simp

theorem involution_alt_type {σ : Perm (Fin 12)} (h : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hσ : σ ∈ alternatingGroup (Fin 12)) :
    σ.cycleType = Multiset.replicate 2 2 ∨ σ.cycleType = Multiset.replicate 4 2 ∨
      σ.cycleType = Multiset.replicate 6 2 := by
  have hs : (-1 : ℤˣ) ^ Multiset.card σ.cycleType = 1 := by
    rw [← sign_involution h]; exact Equiv.Perm.mem_alternatingGroup.1 hσ
  have hpos : 0 < Multiset.card σ.cycleType := by
    rw [Multiset.card_pos]
    exact fun h0 => hne (Equiv.Perm.cycleType_eq_zero.1 h0)
  have hle : 2 * Multiset.card σ.cycleType ≤ 12 := by
    have h1 := involution_cycleType h
    have h2 : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
    have h3 : σ.support.card ≤ 12 := by
      simpa using Finset.card_le_univ σ.support
    rw [h1] at h2
    simp only [Multiset.sum_replicate, smul_eq_mul] at h2
    omega
  have heven : Even (Multiset.card σ.cycleType) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hs
    exact absurd hs (by decide)
  obtain ⟨m, hm⟩ := heven
  have hk : Multiset.card σ.cycleType = 2 ∨ Multiset.card σ.cycleType = 4 ∨
      Multiset.card σ.cycleType = 6 := by omega
  rw [involution_cycleType h]
  rcases hk with hk | hk | hk
  · left; rw [hk]
  · right; left; rw [hk]
  · right; right; rw [hk]

theorem sq_eq_one_of_cycleType_replicate {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    {k : ℕ} (h : σ.cycleType = Multiset.replicate k 2) : σ ^ 2 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [← Equiv.Perm.lcm_cycleType, h]
  apply Multiset.lcm_dvd.2
  intro a ha
  rw [Multiset.eq_of_mem_replicate ha]

theorem mem_alt_of_cycleType_replicate {σ : Perm (Fin 12)} {k : ℕ} (hk : Even k)
    (h : σ.cycleType = Multiset.replicate k 2) : σ ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, h]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  obtain ⟨m, rfl⟩ := hk
  rw [show (m + m) * 2 + (m + m) = 2 * (3 * m) by ring, pow_mul]
  simp

theorem swap_commute_involution {σ : Perm (Fin 12)} (h : σ ^ 2 = 1) (a : Fin 12) :
    σ * swap a (σ a) = swap a (σ a) * σ := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : Perm (Fin 12) => f x) h
    simpa [pow_two] using this
  ext x
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left, hσσ, Equiv.swap_apply_right]
  · by_cases hxb : x = σ a
    · subst hxb
      rw [Equiv.swap_apply_right, hσσ, Equiv.swap_apply_left]
    · have h1 : σ x ≠ a := fun e => hxb (by rw [← e, hσσ])
      have h2 : σ x ≠ σ a := fun e => hxa (σ.injective e)
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem exists_conj_alt {σ τ : Perm (Fin 12)}
    (h : σ ^ 2 = 1) (hne : σ ≠ 1) (hc : σ.cycleType = τ.cycleType) :
    ∃ c ∈ alternatingGroup (Fin 12), c * σ * c⁻¹ = τ := by
  obtain ⟨ρ, hρ⟩ := isConj_iff.1 ((Equiv.Perm.isConj_iff_cycleType_eq).2 hc)
  by_cases hs : sign ρ = 1
  · exact ⟨ρ, Equiv.Perm.mem_alternatingGroup.2 hs, hρ⟩
  · obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
      by_contra hcon
      push Not at hcon
      exact hne (Equiv.ext hcon)
    refine ⟨ρ * swap a (σ a), ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap ha.symm]
      have : sign ρ = -1 := by
        rcases Int.units_eq_one_or (sign ρ) with h1 | h1
        · exact absurd h1 hs
        · exact h1
      rw [this]; decide
    · have hcomm := swap_commute_involution h a
      calc ρ * swap a (σ a) * σ * (ρ * swap a (σ a))⁻¹
          = ρ * (swap a (σ a) * σ * (swap a (σ a))⁻¹) * ρ⁻¹ := by group
        _ = ρ * σ * ρ⁻¹ := by rw [← hcomm]; group
        _ = τ := hρ

theorem card_type_two :
    (Finset.univ.filter fun g : Perm (Fin 12) => g.cycleType = Multiset.replicate 2 2).card =
      1485 := by
  rw [Equiv.Perm.card_of_cycleType]; decide +kernel

theorem card_type_four :
    (Finset.univ.filter fun g : Perm (Fin 12) => g.cycleType = Multiset.replicate 4 2).card =
      51975 := by
  rw [Equiv.Perm.card_of_cycleType]; decide +kernel

theorem card_type_six :
    (Finset.univ.filter fun g : Perm (Fin 12) => g.cycleType = Multiset.replicate 6 2).card =
      10395 := by
  rw [Equiv.Perm.card_of_cycleType]; decide +kernel

end CFSG.Sporadic.HN.Local
