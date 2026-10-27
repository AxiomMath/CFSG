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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL.S2

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem F4_data [Finite F] (hF : Nat.card F = 4) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ω * ω = ω + 1 ∧ (2 : F) = 0 ∧
      ∀ x : F, x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  have hc : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hcard]; norm_num)
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at this
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  have hω3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hcard] at this
  have hωω : ω * ω = ω + 1 := by
    have h1 : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hω1
    · linear_combination h - (ω + 1) * h2
  refine ⟨ω, hω0, hω1, hωω, h2, fun x => ?_⟩
  have h4 : x ^ 4 = x := by
    have := FiniteField.pow_card x
    rwa [hcard] at this
  have hP : x * (x - 1) * (x - ω) * (x - (ω + 1)) = 0 := by
    linear_combination h4 + (x * (x - 1) * (-x + ω * (1 - x))) * h2 + (x * (x - 1)) * hωω
  rcases mul_eq_zero.1 hP with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.1 h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.1 h)))

@[expose] def uSL (b : F) : SL(2, F) := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lSL (b : F) : SL(2, F) := ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two]⟩

theorem uSL_mulVec (b : F) (q : Fin 2 → F) :
    ((uSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q = ![q 0 + b * q 1, q 1] := by
  ext i
  fin_cases i <;> simp [uSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lSL_mulVec (b : F) (q : Fin 2 → F) :
    ((lSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q = ![q 0, b * q 0 + q 1] := by
  ext i
  fin_cases i <;> simp [lSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem uSL_mul (a b : F) : uSL a * uSL b = uSL (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uSL_injective : Function.Injective (uSL : F → SL(2, F)) := by
  intro a b h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uSL] using this

theorem commutant (g : (Fin 2 → F) →+ (Fin 2 → F))
    (hu : ∀ b q, g (((uSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q) =
      ((uSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ g q)
    (hl : ∀ b q, g (((lSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q) =
      ((lSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ g q) :
    ∃ d : F, ∀ q, g q = d • q := by
  have split : ∀ (x y : F), (![x, y] : Fin 2 → F) = ![x, 0] + ![0, y] := by
    intro x y
    ext i
    fin_cases i <;> simp
  have U : ∀ b c : F, (g ![b * c, 0]) 0 = b * (g ![0, c]) 1 ∧ (g ![b * c, 0]) 1 = 0 := by
    intro b c
    have h := hu b ![0, c]
    rw [uSL_mulVec, uSL_mulVec, split, map_add] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨by linear_combination h0, by linear_combination h1⟩
  have L : ∀ b c : F, (g ![0, b * c]) 0 = 0 ∧ (g ![0, b * c]) 1 = b * (g ![c, 0]) 0 := by
    intro b c
    have h := hl b ![c, 0]
    rw [lSL_mulVec, lSL_mulVec, split, map_add] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨by linear_combination h0, by linear_combination h1⟩
  refine ⟨(g ![0, 1]) 1, fun q => ?_⟩
  have hq : q = ![q 0, 0] + ![0, q 1] := by
    rw [← split]
    ext i
    fin_cases i <;> rfl
  have p0 : (g ![q 0, 0]) 0 = q 0 * (g ![0, 1]) 1 := by
    have := (U (q 0) 1).1
    simpa using this
  have p1 : (g ![q 0, 0]) 1 = 0 := by
    have := (U (q 0) 1).2
    simpa using this
  have d1 : (g ![1, 0]) 0 = (g ![0, 1]) 1 := by
    have := (U 1 1).1
    simpa using this
  have r0 : (g ![0, q 1]) 0 = 0 := by
    have := (L (q 1) 1).1
    simpa using this
  have r1 : (g ![0, q 1]) 1 = q 1 * (g ![0, 1]) 1 := by
    have := (L (q 1) 1).2
    rw [d1] at this
    simpa using this
  conv_lhs => rw [hq, map_add]
  ext i
  fin_cases i
  · simp [p0, r0, mul_comm]
  · simp [p1, r1, mul_comm]

@[expose] def wSL : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem wSL_mulVec (q : Fin 2 → F) :
    ((wSL : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q = ![q 1, -q 0] := by
  ext i
  fin_cases i <;> simp [wSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end CFSG.Quasithin.C124.YL.S2
