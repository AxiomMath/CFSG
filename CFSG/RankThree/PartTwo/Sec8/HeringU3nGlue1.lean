module

import TauCeti.GroupTheory.PGroup
import CFSG.RankThree.PartTwo.Sec4.StepsBender
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

namespace CFSG.RankThree.PartTwo.Sec8.HeringU3n

section Lift

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_one_of_normal_two_group {H Θ R : Subgroup G} {s r x : G}
    (hΘH : H ≤ Subgroup.normalizer (Θ : Set G)) (hΘ : Θ ≤ H) (hΘodd : Odd (Nat.card Θ))
    (hR2 : IsPGroup 2 R) (hRH : R ≤ H) (hRs : R ≤ Subgroup.centralizer ({s} : Set G))
    (hRnorm : ∀ g ∈ H, g * s = s * g → ∀ ρ ∈ R, g * ρ * g⁻¹ ∈ R)
    (hr : r ∈ R) (hxH : x ∈ H) (hxs : x * s = s * x)
    (hw : r * x * r⁻¹ * x⁻¹ ∈ Θ) : r * x * r⁻¹ * x⁻¹ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΘ2 : ¬ 2 ∣ Nat.card Θ := by
    have := Nat.odd_iff.mp hΘodd
    omega
  set w := r * x * r⁻¹ * x⁻¹ with hwdef
  have hrs : r * s = s * r := (Subgroup.mem_centralizer_singleton_iff.mp (hRs hr))
  have hrs' : r⁻¹ * s = s * r⁻¹ := by
    calc r⁻¹ * s = r⁻¹ * (s * r) * r⁻¹ := by group
      _ = r⁻¹ * (r * s) * r⁻¹ := by rw [hrs]
      _ = s * r⁻¹ := by group
  have hxs' : x⁻¹ * s = s * x⁻¹ := by
    calc x⁻¹ * s = x⁻¹ * (s * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * s) * x⁻¹ := by rw [hxs]
      _ = s * x⁻¹ := by group
  have hws : w * s = s * w := by
    calc w * s = r * x * (r⁻¹ * (x⁻¹ * s)) := by rw [hwdef]; group
      _ = r * x * (r⁻¹ * (s * x⁻¹)) := by rw [hxs']
      _ = r * x * ((r⁻¹ * s) * x⁻¹) := by group
      _ = r * x * ((s * r⁻¹) * x⁻¹) := by rw [hrs']
      _ = r * (x * s) * (r⁻¹ * x⁻¹) := by group
      _ = r * (s * x) * (r⁻¹ * x⁻¹) := by rw [hxs]
      _ = (r * s) * x * (r⁻¹ * x⁻¹) := by group
      _ = (s * r) * x * (r⁻¹ * x⁻¹) := by rw [hrs]
      _ = s * w := by rw [hwdef]; group
  have hrw : r * w * r⁻¹ = w := by
    have hwH : w ∈ H := hΘ hw
    have h1 : w * r⁻¹ * w⁻¹ ∈ R := hRnorm w hwH hws r⁻¹ (R.inv_mem hr)
    have h2 : r * (w * r⁻¹ * w⁻¹) ∈ R := R.mul_mem hr h1
    have h3 : r * w * r⁻¹ * w⁻¹ ∈ Θ := by
      have : r * w * r⁻¹ ∈ Θ := (Subgroup.mem_normalizer_iff.mp (hΘH (hRH hr)) w).mp hw
      exact Θ.mul_mem this (Θ.inv_mem hw)
    have h4 : r * w * r⁻¹ * w⁻¹ = r * (w * r⁻¹ * w⁻¹) := by group
    have hbot : R ⊓ Θ = ⊥ := by
      rw [inf_comm]
      exact disjoint_iff.mp (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hΘ2 hR2)
    have h5 : r * w * r⁻¹ * w⁻¹ ∈ R ⊓ Θ := ⟨h4 ▸ h2, h3⟩
    rw [hbot, Subgroup.mem_bot] at h5
    calc r * w * r⁻¹ = r * w * r⁻¹ * w⁻¹ * w := by group
      _ = w := by rw [h5]; group
  have hcomm : Commute r w := by
    have : r * w = w * r := by
      calc r * w = r * w * r⁻¹ * r := by group
        _ = w * r := by rw [hrw]
    exact this
  have hxk : ∀ k : ℕ, r ^ k * x * (r ^ k)⁻¹ = w ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : r * x * r⁻¹ = w * x := by rw [hwdef]; group
      calc r ^ (k + 1) * x * (r ^ (k + 1))⁻¹ = r * (r ^ k * x * (r ^ k)⁻¹) * r⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = r * (w ^ k * x) * r⁻¹ := by rw [ih]
        _ = (r * w ^ k * r⁻¹) * (r * x * r⁻¹) := by group
        _ = w ^ k * (w * x) := by
            rw [e1, (hcomm.pow_right k).eq, mul_assoc, mul_assoc]
            group
        _ = w ^ (k + 1) * x := by rw [pow_succ]; group
  obtain ⟨j, hj⟩ := hR2 ⟨r, hr⟩
  have hrj : r ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have h6 := hxk (2 ^ j)
  rw [hrj] at h6
  have h7 : w ^ (2 ^ j) = 1 := by
    have : x = w ^ (2 ^ j) * x := by simpa using h6
    calc w ^ (2 ^ j) = w ^ (2 ^ j) * x * x⁻¹ := by group
      _ = x * x⁻¹ := by rw [← this]
      _ = 1 := by group
  exact CFSG.RankThree.PartTwo.Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_two hΘ2 hw h7

end Lift

end CFSG.RankThree.PartTwo.Sec8.HeringU3n
