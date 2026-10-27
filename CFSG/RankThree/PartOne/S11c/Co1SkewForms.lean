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
public import Mathlib.GroupTheory.Nilpotent
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

open Matrix

@[expose] def co1M0 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 2, 0, 1, 1, 0; 2, 0, 1, 1, 2, 2; 2, 2, 0, 1, 0, 1; 2, 2, 0, 2, 1, 0; 1, 1, 1, 2, 1, 2;
    0, 0, 2, 0, 2, 2]

@[expose] def co1M1 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![2, 2, 1, 0, 0, 0; 0, 2, 1, 2, 0, 2; 1, 1, 0, 1, 2, 0; 1, 0, 2, 1, 0, 1; 1, 2, 2, 0, 2, 1;
    1, 0, 2, 0, 0, 2]

@[expose] def co1SkewVec (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Fin 15 → ZMod 3 :=
  ![Bm 0 1, Bm 0 2, Bm 0 3, Bm 0 4, Bm 0 5, Bm 1 2, Bm 1 3, Bm 1 4, Bm 1 5, Bm 2 3, Bm 2 4,
    Bm 2 5, Bm 3 4, Bm 3 5, Bm 4 5]

@[expose] def co1SkewN : Matrix (Fin 15) (Fin 15) (ZMod 3) :=
  !![1, 2, 2, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 1, 1, 1, 1, 0, 2, 1, 2, 1, 2;
    1, 1, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0;
    1, 1, 1, 1, 0, 2, 1, 0, 1, 2, 2, 1, 1, 1, 2;
    0, 0, 0, 0, 2, 1, 2, 2, 1, 1, 0, 1, 1, 1, 2;
    2, 0, 0, 2, 1, 0, 1, 2, 0, 0, 2, 1, 2, 1, 2;
    2, 0, 0, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1;
    0, 0, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 0, 1;
    2, 1, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0;
    1, 2, 1, 0, 0, 1, 1, 1, 1, 0, 2, 2, 2, 2, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 1;
    1, 0, 2, 2, 0, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1;
    0, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 0, 1;
    1, 2, 2, 0, 0, 0, 1, 2, 0, 1, 1, 0, 1, 0, 0]

@[expose] def co1SkewInv : Matrix (Fin 15) (Fin 15) (ZMod 3) :=
  !![2, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0;
    2, 1, 2, 1, 0, 2, 2, 1, 2, 2, 0, 2, 1, 0, 0;
    0, 1, 1, 0, 2, 2, 1, 0, 0, 1, 1, 1, 0, 2, 2;
    0, 1, 1, 0, 2, 1, 0, 1, 2, 1, 0, 0, 2, 2, 2;
    2, 0, 2, 1, 0, 2, 2, 1, 0, 2, 1, 1, 0, 0, 0;
    0, 2, 2, 1, 0, 1, 2, 1, 0, 0, 1, 0, 2, 0, 0;
    1, 0, 1, 2, 1, 0, 0, 2, 1, 2, 1, 2, 1, 0, 2;
    0, 1, 0, 0, 1, 1, 2, 0, 1, 1, 0, 2, 2, 0, 2;
    2, 0, 2, 0, 2, 2, 1, 0, 1, 0, 1, 2, 1, 1, 0;
    0, 0, 2, 0, 0, 1, 0, 2, 2, 1, 2, 2, 1, 0, 0;
    2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 0, 2, 1, 1;
    1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 0, 1, 1;
    0, 0, 2, 0, 0, 0, 2, 2, 0, 2, 2, 1, 1, 1, 2;
    0, 2, 2, 0, 1, 1, 2, 1, 1, 2, 1, 1, 0, 0, 2;
    0, 1, 1, 0, 0, 1, 0, 1, 2, 1, 1, 1, 2, 0, 1]

theorem co1SkewInv_mul : co1SkewInv * co1SkewN = 1 := by decide +kernel

@[expose] def Co1LowerRel (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  Bm 1 0 = 2 * Bm 0 1 ∧
    Bm 2 0 = 2 * Bm 0 2 ∧
    Bm 3 0 = 2 * Bm 0 3 ∧
    Bm 4 0 = 2 * Bm 0 4 ∧
    Bm 5 0 = 2 * Bm 0 5 ∧
    Bm 2 1 = 2 * Bm 1 2 ∧
    Bm 3 1 = 2 * Bm 1 3 ∧
    Bm 4 1 = 2 * Bm 1 4 ∧
    Bm 5 1 = 2 * Bm 1 5 ∧
    Bm 3 2 = 2 * Bm 2 3 ∧
    Bm 4 2 = 2 * Bm 2 4 ∧
    Bm 5 2 = 2 * Bm 2 5 ∧
    Bm 4 3 = 2 * Bm 3 4 ∧
    Bm 5 3 = 2 * Bm 3 5 ∧
    Bm 5 4 = 2 * Bm 4 5

theorem co1SkewRow0 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 0 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨l10, l20, l30, l40, _, _, _, _, _, l32, l42, _, l43, _, _⟩ := hl
  have e := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l10, l20, l30, l40, l32, l42, l43] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (2 * Bm 0 1 + 2 * Bm 0 2 + 2 * Bm 0 3 + 1 * Bm 0 4 + 1 * Bm 1
      2 + 1 * Bm 1 3 + 4 * Bm 2 3 + 2 * Bm 2 4 + 2 * Bm 3 4) * h3

theorem co1SkewRow1 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 1 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, l21, l31, l41, _, _, _, _, _, _, _⟩ := hl
  have e := congrFun (congrFun h 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l21, l31, l41] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (1 * Bm 0 2) * h3 - (1 * Bm 1 2 + 1 * Bm 1 3 + 1 * Bm 1 4 + 1 * Bm 1 5 +
      1 * Bm 2 5 + 1 * Bm 3 5) * h3

theorem co1SkewRow2 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 2 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨l10, l20, l30, l40, _, l21, l31, l41, _, l32, l42, _, l43, _, _⟩ := hl
  have e := congrFun (congrFun h 0) 3
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l10, l20, l30, l40, l21, l31, l41, l32,
      l42, l43] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 1 + 1 * Bm 0 2 + 1 * Bm 0 3 + 2 * Bm 1 2 + 2 * Bm 1
      3 + 2 * Bm 1 4 + 2 * Bm 2 3 + 2 * Bm 2 4 + 2 * Bm 3 4) * h3

theorem co1SkewRow3 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 3 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨l10, l20, l30, l40, _, l21, l31, l41, _, _, _, _, l43, _, _⟩ := hl
  have e := congrFun (congrFun h 0) 4
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l10, l20, l30, l40, l21, l31, l41, l43] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 1 + 1 * Bm 0 2 + 1 * Bm 0 3 + 2 * Bm 1 2 + 3 * Bm 1
      3 + 2 * Bm 1 4 + 1 * Bm 1 5 + 1 * Bm 2 5 + 1 * Bm 3 4 + 1 * Bm 3 5) * h3

theorem co1SkewRow4 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 4 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, l21, l31, l41, _, l32, l42, _, _, _, _⟩ := hl
  have e := congrFun (congrFun h 0) 5
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l21, l31, l41, l32, l42] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (1 * Bm 0 5) * h3 - (3 * Bm 1 2 + 2 * Bm 1 3 + 2 * Bm 1 4 + 1 * Bm 1 5 +
      1 * Bm 2 3 + 2 * Bm 2 4 + 1 * Bm 2 5 + 1 * Bm 3 4 + 1 * Bm 3 5) * h3

theorem co1SkewRow5 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 5 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, l21, l31, l41, _, _, _, _, _, _, _⟩ := hl
  have e := congrFun (congrFun h 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l21, l31, l41] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 5 + 1 * Bm 1 2 + 1 * Bm 1 3 + 1 * Bm 2 5 + 1 * Bm 3
      5) * h3

theorem co1SkewRow6 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 6 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨l10, _, _, l40, l50, _, _, l41, l51, _, l42, l52, l43, l53, l54⟩ := hl
  have e := congrFun (congrFun h 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l10, l40, l50, l41, l51, l42, l52, l43,
      l53, l54] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (1 * Bm 2 3) * h3 - (1 * Bm 0 5 + 1 * Bm 1 4 + 1 * Bm 1 5 + 1 * Bm 2 5 +
      1 * Bm 3 4 + 2 * Bm 3 5 + 2 * Bm 4 5) * h3

theorem co1SkewRow7 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M0ᵀ * Bm * co1M0 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 7 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, _, _, l41, l51, _, l42, l52, _, _, l54⟩ := hl
  have e := congrFun (congrFun h 2) 5
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M0, hd, l41, l51, l42, l52, l54] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (2 * Bm 1 4 + 3 * Bm 1 5 + 1 * Bm 2 5 + 3 * Bm 4 5) * h3

theorem co1SkewRow8 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M1ᵀ * Bm * co1M1 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 8 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, l20, l30, l40, l50, l21, l31, l41, l51, l32, l42, l52, _, _, l54⟩ := hl
  have e := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M1, hd, l20, l30, l40, l50, l21, l31, l41, l51,
      l32, l42, l52, l54] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 1 + 2 * Bm 0 2 + 1 * Bm 0 3 + 2 * Bm 0 4 + 1 * Bm 0
      5 + 1 * Bm 1 2 + 1 * Bm 1 3 + 1 * Bm 1 4 + 1 * Bm 1 5 + 1 * Bm 2 4 + 1 * Bm 4 5) * h3

theorem co1SkewRow9 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M1ᵀ * Bm * co1M1 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 9 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, l20, l30, l40, l50, l21, l31, l41, l51, _, _, _, l43, l53, l54⟩ := hl
  have e := congrFun (congrFun h 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M1, hd, l20, l30, l40, l50, l21, l31, l41, l51,
      l43, l53, l54] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (2 * Bm 0 3 + 2 * Bm 0 4 + 2 * Bm 0 5 + 2 * Bm 3 4 + 2 * Bm 3
      5 + 2 * Bm 4 5) * h3

theorem co1SkewRow10 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M1ᵀ * Bm * co1M1 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 10 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, l21, l31, l41, l51, l32, l42, l52, l43, l53, _⟩ := hl
  have e := congrFun (congrFun h 0) 3
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M1, hd, l21, l31, l41, l51, l32, l42, l52, l43,
      l53] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 1 + 1 * Bm 1 2 + 1 * Bm 1 3 + 1 * Bm 1 4 + 1 * Bm 1
      5 + 1 * Bm 2 3) * h3

theorem co1SkewRow11 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M1ᵀ * Bm * co1M1 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 11 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, _, _, _, _, l32, l42, l52, _, _, l54⟩ := hl
  have e := congrFun (congrFun h 0) 4
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M1, hd, l32, l42, l52, l54] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 2 + 1 * Bm 0 4 + 1 * Bm 2 3 + 2 * Bm 2 4 + 1 * Bm 2
      5 + 1 * Bm 4 5) * h3

theorem co1SkewRow12 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M1ᵀ * Bm * co1M1 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 12 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, l21, l31, l41, l51, _, _, _, l43, l53, l54⟩ := hl
  have e := congrFun (congrFun h 0) 5
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M1, hd, l21, l31, l41, l51, l43, l53, l54] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 1 + 1 * Bm 0 5 + 1 * Bm 1 2 + 1 * Bm 1 3 + 1 * Bm 1
      4 + 1 * Bm 1 5 + 1 * Bm 3 4 + 1 * Bm 3 5 + 1 * Bm 4 5) * h3

theorem co1SkewRow13 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M1ᵀ * Bm * co1M1 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 13 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨l10, l20, _, l40, _, l21, _, l41, _, _, _, _, l43, _, _⟩ := hl
  have e := congrFun (congrFun h 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M1, hd, l10, l20, l40, l21, l41, l43] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (2 * Bm 0 1 + 1 * Bm 0 3 + 2 * Bm 0 4 + 1 * Bm 0 5 + 1 * Bm 1
      3 + 2 * Bm 1 4 + 1 * Bm 1 5 + 2 * Bm 3 4 + 1 * Bm 4 5) * h3

theorem co1SkewRow14 (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3)) (hd : ∀ i, Bm i i = 0)
    (hl : Co1LowerRel Bm) (h : co1M1ᵀ * Bm * co1M1 = Bm) :
    (co1SkewN *ᵥ co1SkewVec Bm) 14 = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  obtain ⟨_, _, _, _, _, l21, _, l41, _, _, l42, _, l43, _, _⟩ := hl
  have e := congrFun (congrFun h 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_succ, co1M1, hd, l21, l41, l42, l43] at e
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, co1SkewN, co1SkewVec]
  linear_combination e + (0) * h3 - (1 * Bm 0 1 + 2 * Bm 1 2 + 2 * Bm 1 4 + 1 * Bm 2 4 + 1 * Bm 3
      4) * h3

theorem co1_skew_invariant_zero (Bm : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (hd : ∀ i, Bm i i = 0) (hs : ∀ i j, Bm i j = - Bm j i)
    (h0 : co1M0ᵀ * Bm * co1M0 = Bm) (h1 : co1M1ᵀ * Bm * co1M1 = Bm) : Bm = 0 := by
  have hneg : ∀ x : ZMod 3, -x = 2 * x := by decide
  have hl : Co1LowerRel Bm := by
    refine ⟨by rw [hs 1 0, hneg], by rw [hs 2 0, hneg], by rw [hs 3 0, hneg],
      by rw [hs 4 0, hneg], by rw [hs 5 0, hneg], by rw [hs 2 1, hneg], by rw [hs 3 1, hneg],
      by rw [hs 4 1, hneg], by rw [hs 5 1, hneg], by rw [hs 3 2, hneg], by rw [hs 4 2, hneg],
      by rw [hs 5 2, hneg], by rw [hs 4 3, hneg], by rw [hs 5 3, hneg], by rw [hs 5 4, hneg]⟩
  have hN : co1SkewN *ᵥ co1SkewVec Bm = 0 := by
    ext r
    fin_cases r
    · exact co1SkewRow0 Bm hd hl h0
    · exact co1SkewRow1 Bm hd hl h0
    · exact co1SkewRow2 Bm hd hl h0
    · exact co1SkewRow3 Bm hd hl h0
    · exact co1SkewRow4 Bm hd hl h0
    · exact co1SkewRow5 Bm hd hl h0
    · exact co1SkewRow6 Bm hd hl h0
    · exact co1SkewRow7 Bm hd hl h0
    · exact co1SkewRow8 Bm hd hl h1
    · exact co1SkewRow9 Bm hd hl h1
    · exact co1SkewRow10 Bm hd hl h1
    · exact co1SkewRow11 Bm hd hl h1
    · exact co1SkewRow12 Bm hd hl h1
    · exact co1SkewRow13 Bm hd hl h1
    · exact co1SkewRow14 Bm hd hl h1
  have hx : co1SkewVec Bm = 0 := by
    calc co1SkewVec Bm = (co1SkewInv * co1SkewN) *ᵥ co1SkewVec Bm := by
          rw [co1SkewInv_mul, Matrix.one_mulVec]
      _ = co1SkewInv *ᵥ (co1SkewN *ᵥ co1SkewVec Bm) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hN, Matrix.mulVec_zero]

  have x01 : Bm 0 1 = 0 := congrFun hx 0
  have x02 : Bm 0 2 = 0 := congrFun hx 1
  have x03 : Bm 0 3 = 0 := congrFun hx 2
  have x04 : Bm 0 4 = 0 := congrFun hx 3
  have x05 : Bm 0 5 = 0 := congrFun hx 4
  have x12 : Bm 1 2 = 0 := congrFun hx 5
  have x13 : Bm 1 3 = 0 := congrFun hx 6
  have x14 : Bm 1 4 = 0 := congrFun hx 7
  have x15 : Bm 1 5 = 0 := congrFun hx 8
  have x23 : Bm 2 3 = 0 := congrFun hx 9
  have x24 : Bm 2 4 = 0 := congrFun hx 10
  have x25 : Bm 2 5 = 0 := congrFun hx 11
  have x34 : Bm 3 4 = 0 := congrFun hx 12
  have x35 : Bm 3 5 = 0 := congrFun hx 13
  have x45 : Bm 4 5 = 0 := congrFun hx 14
  obtain ⟨l10, l20, l30, l40, l50, l21, l31, l41, l51, l32, l42, l52, l43, l53, l54⟩ := hl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hd, x01, x02, x03, x04, x05, x12, x13, x14, x15, x23,
      x24, x25, x34, x35, x45, l10, l20, l30, l40, l50, l21, l31, l41, l51, l32, l42, l52, l43,
      l53, l54]


end CFSG.RankThree.PartOne
