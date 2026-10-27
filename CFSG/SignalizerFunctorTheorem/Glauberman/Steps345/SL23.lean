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

namespace CFSG.SignalizerFunctorTheorem.Glauberman

theorem exists_orderOf_eq_six_sl_two_three :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), orderOf x = 6 := by
  refine ⟨⟨!![2, 2; 0, 2], by rw [Matrix.det_fin_two_of]; decide⟩, ?_⟩
  refine (orderOf_eq_iff (by norm_num)).2 ⟨?_, ?_⟩
  · decide
  · decide

private theorem exists_conj_ne_of_pow_three_eq_one
    (t : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (h3 : t ^ 3 = 1) (h1 : t ≠ 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      g * t * g⁻¹ ≠ 1 ∧ g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ ≠ t * t := by
  revert t
  decide

theorem eq_bot_of_normal_of_odd_card_sl_two_three
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) [N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hdvd : Nat.card N ∣ 24 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have h13 : Nat.card N = 1 ∨ Nat.card N = 3 := by
    have key : ∀ n : ℕ, n ≤ 24 → n ∣ 24 → Odd n → n = 1 ∨ n = 3 := by decide
    exact key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hodd
  rcases h13 with h | h
  · exact Subgroup.eq_bot_of_card_eq N h
  · exfalso
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 (by rw [h])
    obtain ⟨s, hsN, hs⟩ : ∃ s ∈ N, orderOf s = 3 := ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht⟩
    have h3 : s ^ 3 = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hs] at this
    have h1 : s ≠ 1 := by
      rintro rfl
      simp at hs
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_conj_ne_of_pow_three_eq_one s h3 h1
    have hmem : g * s * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance s hsN g
    have hzp : Subgroup.zpowers s = N := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.2 hsN
      · rw [h, Nat.card_zpowers, hs]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((SetLike.ext_iff.1 hzp _).2 hmem)
    rw [← zpow_mod_orderOf, hs] at hk
    obtain h0 | h0 | h0 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
        k % ((3 : ℕ) : ℤ) = 2 := by omega
    · rw [h0] at hk
      exact hg1 (by simpa using hk.symm)
    · rw [h0] at hk
      exact hg2 (by simpa using hk.symm)
    · rw [h0] at hk
      exact hg3 (by simpa [sq] using hk.symm)

end CFSG.SignalizerFunctorTheorem.Glauberman
