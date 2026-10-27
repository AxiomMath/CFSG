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
public import Mathlib.Data.Nat.Prime.Factorial
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

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem not_dvd_factorial_of_lt {s n : ℕ} (hs : s.Prime) (h : n < s) : ¬ s ∣ n.factorial := by
  intro hd
  exact absurd ((Nat.Prime.dvd_factorial hs).1 hd) (by omega)

theorem not_pow_dvd_factorial_twentyeight {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (h2 : ℓ = 2 → 3 ≤ d) (h3 : ℓ = 3 → 2 ≤ d) : ¬ ℓ ^ (12 * d) ∣ (28).factorial := by
  intro h
  by_cases hle : ℓ ≤ 28
  · have h12 : ℓ ^ 12 ∣ (28).factorial := (pow_dvd_pow ℓ (by omega : 12 ≤ 12 * d)).trans h
    interval_cases ℓ
    all_goals first
      | (exfalso; revert hℓ; norm_num; done)
      | (have := h2 rfl
         have h36 : 2 ^ 36 ∣ (28).factorial :=
           (pow_dvd_pow 2 (by omega : 36 ≤ 12 * d)).trans h
         revert h36; decide)
      | (have := h3 rfl
         have h24 : 3 ^ 24 ∣ (28).factorial :=
           (pow_dvd_pow 3 (by omega : 24 ≤ 12 * d)).trans h
         revert h24; decide)
      | (revert h12; decide)
  · have hdvd : ℓ ∣ (28).factorial :=
      (dvd_pow_self ℓ (by omega : 12 * d ≠ 0)).trans h
    exact not_dvd_factorial_of_lt hℓ (by omega) hdvd

theorem not_pow_dvd_factorial_seventyeight {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (h2 : ℓ = 2 → 3 ≤ d) (h3 : ℓ = 3 → 2 ≤ d) : ¬ ℓ ^ (36 * d) ∣ (78).factorial := by
  intro h
  by_cases hle : ℓ ≤ 78
  · have h36 : ℓ ^ 36 ∣ (78).factorial := (pow_dvd_pow ℓ (by omega : 36 ≤ 36 * d)).trans h
    interval_cases ℓ
    all_goals first
      | (exfalso; revert hℓ; norm_num; done)
      | (have := h2 rfl
         have h108 : 2 ^ 108 ∣ (78).factorial :=
           (pow_dvd_pow 2 (by omega : 108 ≤ 36 * d)).trans h
         revert h108; decide)
      | (have := h3 rfl
         have h72 : 3 ^ 72 ∣ (78).factorial :=
           (pow_dvd_pow 3 (by omega : 72 ≤ 36 * d)).trans h
         revert h72; decide)
      | (revert h36; decide)
  · have hdvd : ℓ ∣ (78).factorial :=
      (dvd_pow_self ℓ (by omega : 36 * d ≠ 0)).trans h
    exact not_dvd_factorial_of_lt hℓ (by omega) hdvd

theorem exists_prime_pow_dvd_not_dvd_factorial_D4 {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (hne : ¬ (ℓ = 2 ∧ d = 1)) :
    ∃ s e : ℕ, s.Prime ∧ s ^ e ∣ (ℓ ^ d) ^ 12 * ((ℓ ^ d) ^ 2 - 1) * ((ℓ ^ d) ^ 6 - 1) *
        ((ℓ ^ d) ^ 8 + (ℓ ^ d) ^ 4 + 1) ∧ ¬ s ^ e ∣ (28).factorial := by
  by_cases h22 : ℓ = 2 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := h22
    exact ⟨241, 1, by norm_num, by norm_num, by decide⟩
  by_cases h31 : ℓ = 3 ∧ d = 1
  · obtain ⟨rfl, rfl⟩ := h31
    exact ⟨73, 1, by norm_num, by norm_num, by decide⟩
  refine ⟨ℓ, 12 * d, hℓ, ?_, not_pow_dvd_factorial_twentyeight hℓ hd ?_ ?_⟩
  · rw [pow_mul']
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _) _
  · intro h
    by_contra h'
    exact hne ⟨h, by omega⟩ |>.elim
  · intro h
    by_contra h'
    exact h31 ⟨h, by omega⟩

theorem pow_pow_add_mul_eq {k : Type*} [Field k] [Finite k] {ℓ m : ℕ}
    (hk : Nat.card k = ℓ ^ m) (a b : ℕ) (c : k) : c ^ ℓ ^ (m * a + b) = c ^ ℓ ^ b := by
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = ℓ ^ m := by rw [← Nat.card_eq_fintype_card, hk]
  have he : ℓ ^ (m * a + b) = (ℓ ^ m) ^ a * ℓ ^ b := by rw [pow_add, pow_mul]
  rw [he, pow_mul, ← hq, FiniteField.pow_card_pow]

theorem exists_subgroup_card_not_dvd_factorial {G : Type*} [Group G] [Finite G] {N n s e : ℕ}
    (hN : Nat.card G = N) (hs : s.Prime) (hdvd : s ^ e ∣ N) (hn : ¬ s ^ e ∣ n.factorial) :
    ∃ R : Subgroup G, ¬ Nat.card R ∣ n.factorial := by
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime s (hN ▸ hdvd)
  exact ⟨R, by rw [hR]; exact hn⟩

theorem exists_le_subgroup_card_not_dvd_factorial {C : Type*} [Group C] {J : Subgroup C}
    {n : ℕ} (h : ∃ R : Subgroup J, ¬ Nat.card R ∣ n.factorial) :
    ∃ R : Subgroup C, R ≤ J ∧ ¬ Nat.card R ∣ n.factorial := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.map J.subtype, Subgroup.map_subtype_le R, ?_⟩
  rwa [show Nat.card (R.map J.subtype) = Nat.card R from
    Nat.card_congr (R.equivMapOfInjective J.subtype J.subtype_injective).toEquiv.symm]

end CFSG.SignalizerFunctorTheorem.CatalogBridge
