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

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped commutatorElement

theorem commutator_mem_oddPart_of_fixed_two_part {C : Type*} [Group C] {Q Qodd : Subgroup C}
    [Qodd.Normal] {p : ℕ} (hp : Odd p) {α : C} (hα : ∃ i : ℕ, orderOf α = p ^ i)
    (hfix : ∀ c ∈ Q, ⁅α, c⁆ ∈ Qodd) (hQ2 : ∀ c ∈ Q, ∃ k : ℕ, c ^ 2 ^ k ∈ Qodd) {s : C}
    (hc : ⁅s, α⁆ ∈ Q) : ⁅s, α⁆ ∈ Qodd := by
  set c : C := ⁅s, α⁆ with hcdef
  set m : ℕ := orderOf α with hm
  obtain ⟨i, hi⟩ := hα
  have hmodd : Odd m := by rw [hi]; exact hp.pow
  let π : C →* C ⧸ Qodd := QuotientGroup.mk' Qodd
  have hcomm : π α * π c = π c * π α := by
    have h := hfix c hc
    rw [commutatorElement_def] at h
    have h1 : π (α * c * α⁻¹ * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π α * π c = π α * π c * (π α)⁻¹ * (π c)⁻¹ * (π c * π α) := by group
      _ = π c * π α := by rw [h1, one_mul]
  have hσ : π α * (π s)⁻¹ * (π α)⁻¹ = (π s)⁻¹ * π c := by
    rw [hcdef, commutatorElement_def]
    simp only [map_mul, map_inv]
    group
  have hiter : ∀ j : ℕ, (π α) ^ j * (π s)⁻¹ * ((π α) ^ j)⁻¹ = (π s)⁻¹ * (π c) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : π α * (π c) ^ j * (π α)⁻¹ = (π c) ^ j := by
        have : Commute (π α) (π c) := hcomm
        rw [(this.pow_right j).eq, mul_inv_cancel_right]
      calc (π α) ^ (j + 1) * (π s)⁻¹ * ((π α) ^ (j + 1))⁻¹
          = π α * ((π α) ^ j * (π s)⁻¹ * ((π α) ^ j)⁻¹) * (π α)⁻¹ := by group
        _ = π α * ((π s)⁻¹ * (π c) ^ j) * (π α)⁻¹ := by rw [ih]
        _ = (π α * (π s)⁻¹ * (π α)⁻¹) * (π α * (π c) ^ j * (π α)⁻¹) := by group
        _ = (π s)⁻¹ * (π c) * (π c) ^ j := by rw [hσ, hcj]
        _ = (π s)⁻¹ * (π c) ^ (j + 1) := by rw [pow_succ']; group
  have hcm : (π c) ^ m = 1 := by
    have h := hiter m
    have hαm : (π α) ^ m = 1 := by rw [← map_pow, hm, pow_orderOf_eq_one, map_one]
    rw [hαm, one_mul, inv_one, mul_one] at h
    exact (mul_eq_left.mp h.symm : ((π c) ^ m) = 1)
  obtain ⟨k, hk⟩ := hQ2 c hc
  have hck : (π c) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have hord : orderOf (π c) ∣ Nat.gcd m (2 ^ k) := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcm)
    (orderOf_dvd_of_pow_eq_one hck)
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hmodd)
  have h1 : orderOf (π c) = 1 := by
    rw [hcop.gcd_eq_one] at hord
    exact Nat.dvd_one.mp hord
  exact (QuotientGroup.eq_one_iff c).mp (orderOf_eq_one_iff.mp h1)

theorem commutator_subgroup_odd_of_fixed_two_part {C : Type*} [Group C] [Finite C]
    {S A Q Qodd : Subgroup C} [Qodd.Normal] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hA : IsPGroup p A)
    (hfix : ∀ α ∈ A, ∀ c ∈ Q, ⁅α, c⁆ ∈ Qodd) (hQ2 : ∀ c ∈ Q, ∃ k : ℕ, c ^ 2 ^ k ∈ Qodd)
    (hSA : ⁅S, A⁆ ≤ Q) (hodd : Odd (Nat.card Qodd)) :
    ⁅S, A⁆ ≤ Qodd ∧ Odd (Nat.card (⁅S, A⁆ : Subgroup C)) := by
  have hle : ⁅S, A⁆ ≤ Qodd := by
    rw [Subgroup.commutator_le]
    intro s hs α hα
    refine commutator_mem_oddPart_of_fixed_two_part hp ?_ (hfix α hα) hQ2
      (hSA (Subgroup.commutator_mem_commutator hs hα))
    obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨α, hα⟩
    exact ⟨i, by rw [← hi, ← Subgroup.orderOf_coe]⟩
  exact ⟨hle, Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)⟩

end CFSG.RankThree.PartOne
