module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.StrictCombination
public import Mathlib.Analysis.InnerProductSpace.OfNorm
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
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

universe indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem complex_unit_average_rigidity
    {IndexType : Type indexUniverse} [Fintype IndexType] [Nonempty IndexType]
    (values : IndexType → ℂ) (unit_norm : ∀ index, ‖values index‖ = 1)
    (average_large : 1 ≤ ‖(∑ index, values index) / (Fintype.card IndexType : ℂ)‖) :
    ∀ index, values index = (∑ selected, values selected) / (Fintype.card IndexType : ℂ) := by
  classical
  have card_positive : 0 < Fintype.card IndexType := Fintype.card_pos
  have real_card_positive : 0 < (Fintype.card IndexType : ℝ) := by exact_mod_cast card_positive
  have weight_ne : (Fintype.card IndexType : ℝ)⁻¹ ≠ 0 := inv_ne_zero real_card_positive.ne'
  have weights_sum : (∑ _index : IndexType, (Fintype.card IndexType : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_inv_cancel₀ real_card_positive.ne']
  have average_equal : (∑ index, (Fintype.card IndexType : ℝ)⁻¹ • values index) =
      (∑ index, values index) / (Fintype.card IndexType : ℂ) := by
    rw [← Finset.smul_sum, Complex.real_smul, Complex.ofReal_inv]
    simp only [Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]
  have all_equal : ∀ first second, values first = values second := by
    intro first second
    by_contra different
    have small := norm_sum_lt_of_strictConvexSpace
      (t := Finset.univ) (w := fun _index : IndexType => (Fintype.card IndexType : ℝ)⁻¹)
      (r := 1) (z := values)
      (fun _index _member => le_of_lt (inv_pos.mpr real_card_positive)) weights_sum
      (Finset.mem_univ first) (Finset.mem_univ second) different weight_ne weight_ne
      (fun index _member => (unit_norm index).le)
    rw [average_equal] at small
    exact (not_lt_of_ge average_large) small
  intro index
  have sum_equal : (∑ selected, values selected) = (Fintype.card IndexType : ℂ) * values index := by
    rw [Finset.sum_eq_card_nsmul (fun selected _member => all_equal selected index), nsmul_eq_mul]
    rfl
  have complex_card_ne : (Fintype.card IndexType : ℂ) ≠ 0 := by exact_mod_cast card_positive.ne'
  rw [sum_equal, mul_div_cancel_left₀ _ complex_card_ne]

theorem integral_root_of_unity_average_rigidity
    {IndexType : Type indexUniverse} [Fintype IndexType] [Nonempty IndexType]
    (values : IndexType → ℂ)
    (roots : ∀ index, ∃ exponent : ℕ, 0 < exponent ∧ values index ^ exponent = 1)
    (integral : IsIntegral ℤ ((∑ index, values index) / (Fintype.card IndexType : ℂ))) :
    (∑ index, values index) / (Fintype.card IndexType : ℂ) = 0 ∨
      ∀ index, values index = (∑ selected, values selected) / (Fintype.card IndexType : ℂ) := by
  classical
  let field := IntermediateField.adjoin ℚ (Set.range values)
  let : Finite (Set.range values) := (Set.finite_range values).to_subtype
  have range_integral : ∀ value ∈ Set.range values, IsIntegral ℚ value := by
    rintro _value ⟨index, rfl⟩
    obtain ⟨exponent, positive, power⟩ := roots index
    apply IsIntegral.of_pow positive
    rw [power]
    exact isIntegral_one
  let : FiniteDimensional ℚ field := IntermediateField.finiteDimensional_adjoin range_integral
  let : NumberField field := NumberField.mk
  let lifted : IndexType → field := fun index =>
    ⟨values index, IntermediateField.subset_adjoin ℚ (Set.range values) ⟨index, rfl⟩⟩
  let average : field := (∑ index, lifted index) / (Fintype.card IndexType : field)
  have average_coe : (algebraMap field ℂ) average =
      (∑ index, values index) / (Fintype.card IndexType : ℂ) := by
    simp [average, lifted]
  have average_integral : IsIntegral ℤ average := IsIntegral.tower_bot_of_field (by rwa [average_coe])
  by_cases average_zero : (∑ index, values index) / (Fintype.card IndexType : ℂ) = 0
  · exact Or.inl average_zero
  right
  have average_ne : average ≠ 0 := by
    intro equal
    apply average_zero
    rw [← average_coe, equal, map_zero]
  let integer_average : NumberField.RingOfIntegers field := ⟨average, average_integral⟩
  have integer_average_ne : integer_average ≠ 0 := by
    intro equal
    exact average_ne (congrArg (fun value : NumberField.RingOfIntegers field => (value : field)) equal)
  obtain ⟨embedding, large⟩ := NumberField.exists_conjugate_one_le_norm integer_average_ne
  have lifted_power : ∀ index, ∃ exponent : ℕ, 0 < exponent ∧ lifted index ^ exponent = 1 := by
    intro index
    obtain ⟨exponent, positive, power⟩ := roots index
    refine ⟨exponent, positive, ?_⟩
    exact (algebraMap field ℂ).injective (by simpa [lifted] using power)
  have embedded_norm : ∀ index, ‖embedding (lifted index)‖ = 1 := by
    intro index
    obtain ⟨exponent, positive, power⟩ := lifted_power index
    apply Complex.norm_eq_one_of_pow_eq_one (n := exponent) _ positive.ne'
    simpa only [map_pow, map_one] using congrArg embedding power
  have embedded_average : embedding average =
      (∑ index, embedding (lifted index)) / (Fintype.card IndexType : ℂ) := by
    simp only [average, map_div₀, map_sum, map_natCast]
  have embedded_large : 1 ≤ ‖(∑ index, embedding (lifted index)) / (Fintype.card IndexType : ℂ)‖ := by
    rw [← embedded_average]
    exact large
  have constant := complex_unit_average_rigidity (fun index => embedding (lifted index)) embedded_norm embedded_large
  intro index
  have equal : lifted index = average := embedding.injective (by rw [embedded_average]; exact constant index)
  calc
    values index = (algebraMap field ℂ) (lifted index) := rfl
    _ = (algebraMap field ℂ) average := congrArg (algebraMap field ℂ) equal
    _ = _ := average_coe

end CFSG.SignalizerFunctor.Helpers
