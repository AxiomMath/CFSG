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

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

variable {F : Type} [Field F] [CharP F 2]

theorem exists_ne_zero_ne_one_sq_add [Finite F] (h8 : 8 ≤ Nat.card F) :
    ∃ s : F, s ≠ 0 ∧ s ≠ 1 ∧ s ^ 2 + s + 1 ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  by_contra hno
  push Not at hno
  by_cases hex : ∃ s₀ : F, s₀ ^ 2 + s₀ + 1 = 0
  · obtain ⟨s₀, hs₀⟩ := hex
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1, s₀, s₀ + 1} := by
      intro s _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h0 : s = 0
      · exact Or.inl h0
      by_cases h1 : s = 1
      · exact Or.inr (Or.inl h1)
      have hs := hno s h0 h1
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have hfac : (s - s₀) * (s - s₀ - 1) = 0 := by
        linear_combination hs - hs₀ + (-s * s₀ + s₀ ^ 2 - s + s₀) * h2
      rcases mul_eq_zero.mp hfac with h | h
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
      · right; right; right
        have : s = s₀ + 1 := by linear_combination h
        exact this
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
    have : ({0, 1, s₀, s₀ + 1} : Finset F).card ≤ 4 := Finset.card_le_four
    omega
  · push Not at hex
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro s _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h0 : s = 0
      · exact Or.inl h0
      by_cases h1 : s = 1
      · exact Or.inr h1
      exact absurd (hno s h0 h1) (hex s)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
    have : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega

theorem eq_one_of_invariant_biadditive [Finite F] (h8 : 8 ≤ Nat.card F) {W : Type*}
    [Group W] (β : F → F → W) (hl : ∀ x x' y, β (x + x') y = β x y * β x' y)
    (hr : ∀ x y y', β x (y + y') = β x y * β x y') (hsq : ∀ x y, β x y ^ 2 = 1)
    (hinv : ∀ c x y, c ≠ 0 → β (c * x) (c * y) = β x y) : ∀ x y, β x y = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hL : ∀ x y, y ≠ 0 → β x y = β (x / y) 1 := fun x y hy => by
    have h := hinv y⁻¹ x y (inv_ne_zero hy)
    rw [inv_mul_cancel₀ hy, ← div_eq_inv_mul] at h
    exact h.symm
  obtain ⟨s, hs0, hs1, hs2⟩ := exists_ne_zero_ne_one_sq_add h8
  have h1s : 1 + s ≠ 0 := by
    intro h
    apply hs1
    linear_combination h - h2
  set μ : F := 1 / (1 + s) + 1 + 1 / s with hμdef
  have hμ : μ ≠ 0 := by
    intro h0
    apply hs2
    have : μ * (s * (1 + s)) = s ^ 2 + s + 1 := by
      rw [hμdef]
      have e1 : 1 / (1 + s) * (s * (1 + s)) = s := by field_simp
      have e2 : 1 / s * (s * (1 + s)) = 1 + s := by field_simp
      calc (1 / (1 + s) + 1 + 1 / s) * (s * (1 + s)) =
          1 / (1 + s) * (s * (1 + s)) + s * (1 + s) + 1 / s * (s * (1 + s)) := by ring
        _ = s + s * (1 + s) + (1 + s) := by rw [e1, e2]
        _ = s ^ 2 + s + 1 := by linear_combination s * h2
    rw [← this, h0, zero_mul]
  have hLμ : ∀ x, β (x * μ) 1 = 1 := by
    intro x
    have h1 := hr x 1 s
    rw [hL x (1 + s) h1s, hL x 1 one_ne_zero, hL x s hs0] at h1
    have hx : x * μ = x / (1 + s) + (x / 1 + x / s) := by
      rw [hμdef]
      ring
    rw [hx, hl, hl, ← h1, ← sq, hsq]
  intro x y
  by_cases hy : y = 0
  · have h0 := hr x 0 0
    rw [add_zero] at h0
    have : β x 0 * β x 0 = β x 0 * 1 := by rw [mul_one]; exact h0.symm
    rw [hy]
    exact mul_left_cancel this
  · rw [hL x y hy]
    have := hLμ (x / y / μ)
    rwa [div_mul_cancel₀ _ hμ] at this

end CFSG.Quasithin.Vol2.Ch11.SecH
