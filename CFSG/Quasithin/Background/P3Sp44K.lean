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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.Quasithin

namespace G11

namespace G118

variable {K : Type} [Field K] [Finite K]

theorem sp44_charTwo (hK : Nat.card K = 4) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard

theorem sp44_pow_three (hK : Nat.card K = 4) (a : K) (ha : a ≠ 0) : a ^ 3 = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem sp44_exists_omega (hK : Nat.card K = 4) : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  classical
  have := Fintype.ofFinite K
  have h4 : 2 < Fintype.card K := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨ω, hω0, hω1, ?_⟩
  have h3 := sp44_pow_three hK ω hω0
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hω1
  · exact h

theorem sp44_pow_four (hK : Nat.card K = 4) (a : K) : a ^ 4 = a := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem sp44_cases (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (t : K) :
    t = 0 ∨ t = 1 ∨ t = ω ∨ t = ω ^ 2 := by
  have h4 := sp44_pow_four hK t
  have h : t * (t - 1) * (t - ω) * (t - ω ^ 2) = 0 := by
    linear_combination h4 + t * (t - 1) * (ω - 1 - t) * hω
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.1 h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.1 h)))

theorem sp44_ringHom_cases (hK : Nat.card K = 4) (θ : K →+* K) :
    (∀ t, θ t = t) ∨ (∀ t, θ t = t ^ 2) := by
  obtain ⟨ω, hω0, hω1, hω⟩ := sp44_exists_omega hK
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hθω : (θ ω) ^ 2 + θ ω + 1 = 0 := by
    have := congrArg θ hω
    simpa using this
  have hprod : (θ ω - ω) * (θ ω - ω ^ 2) = 0 := by
    linear_combination hθω + (ω - 1 - θ ω) * hω
  rcases mul_eq_zero.1 hprod with h | h
  · left
    have hω' : θ ω = ω := sub_eq_zero.1 h
    intro t
    rcases sp44_cases hK hω t with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact hω'
    · rw [map_pow, hω']
  · right
    have hω' : θ ω = ω ^ 2 := sub_eq_zero.1 h
    intro t
    rcases sp44_cases hK hω t with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact hω'
    · rw [map_pow, hω']

end G118

end G11

end CFSG.Quasithin
