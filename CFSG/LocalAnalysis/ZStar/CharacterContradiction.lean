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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace ZStar.CharacterContradiction

universe u v

section StepVI

variable {k : Type u} [Field k] [CharZero k]

private theorem normalized_value_eq_neg_one {f_t f_s f_ts : k}
    (h₁ : f_t * f_s = f_ts) (h₂ : f_t * f_ts = f_s)
    (hfs : f_s ≠ 0) (hft : f_t ≠ 1) :
    f_t = -1 := by
  have hsquare : f_t * f_t = 1 := by
    apply mul_right_cancel₀ hfs
    calc
      (f_t * f_t) * f_s = f_t * (f_t * f_s) := mul_assoc _ _ _
      _ = f_t * f_ts := by rw [h₁]
      _ = f_s := h₂
      _ = 1 * f_s := (one_mul f_s).symm
  rcases mul_self_eq_one_iff.mp hsquare with h | h
  · exact (hft h).elim
  · exact h

theorem character_value_eq_neg_degree {degree χt χs χts : k}
    (hdegree : degree ≠ 0)
    (h₁ : χt * χs = degree * χts)
    (h₂ : χt * χts = degree * χs)
    (hχs : χs ≠ 0) (hχt : χt ≠ degree) :
    χt = -degree := by
  have hn₁ : χt / degree * (χs / degree) = χts / degree := by
    field_simp [hdegree]
    simpa [mul_comm] using h₁
  have hn₂ : χt / degree * (χts / degree) = χs / degree := by
    field_simp [hdegree]
    simpa [mul_comm] using h₂
  have hns : χs / degree ≠ 0 := div_ne_zero hχs hdegree
  have hnt : χt / degree ≠ 1 := by
    exact fun h => hχt ((div_eq_one_iff_eq hdegree).mp h)
  have hneg : χt / degree = -1 :=
    normalized_value_eq_neg_one hn₁ hn₂ hns hnt
  have hmul := (div_eq_iff hdegree).mp hneg
  simpa using hmul

end StepVI

section StepVII

variable {k : Type u} [Field k] [CharZero k]
variable {ι : Type v} [Fintype ι]

theorem finite_sum_stepVII_contradiction (triv : ι)
    (χσ χt χ1 : ι → k)
    (htriv : χσ triv * (χt triv + χ1 triv) = 2)
    (hother : ∀ i : ι, i ≠ triv → χσ i = 0 ∨ χt i = -χ1 i)
    (hort_t : ∑ i : ι, χσ i * χt i = 0)
    (hort_1 : ∑ i : ι, χσ i * χ1 i = 0) :
    False := by
  classical
  have hsum_zero : ∑ i : ι, χσ i * (χt i + χ1 i) = 0 := by
    calc
      (∑ i : ι, χσ i * (χt i + χ1 i)) =
          (∑ i : ι, χσ i * χt i) + (∑ i : ι, χσ i * χ1 i) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ = 0 := by rw [hort_t, hort_1, add_zero]
  have hsum_two : ∑ i : ι, χσ i * (χt i + χ1 i) = 2 := by
    rw [Finset.sum_eq_single triv]
    · exact htriv
    · intro i _ hi
      rcases hother i hi with hiσ | hit
      · simp [hiσ]
      · simp [hit]
    · simp
  rw [hsum_two] at hsum_zero
  norm_num at hsum_zero

end StepVII

end ZStar.CharacterContradiction

end CFSG
