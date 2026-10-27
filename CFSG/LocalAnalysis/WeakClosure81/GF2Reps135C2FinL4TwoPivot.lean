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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix

theorem linearIndependent_of_pivots {d n : ℕ} (y : Fin n → (Fin d → ZMod 2)) (p : Fin n → Fin d)
    (h1 : ∀ k, y k (p k) = 1) (h2 : ∀ k j, k < j → y j (p k) = 0) :
    LinearIndependent (ZMod 2) y := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ m : ℕ, ∀ k : Fin n, k.val = m → g k = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk
      have hcoord := congrFun hg (p k)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      rw [Finset.sum_eq_single k] at hcoord
      · rw [h1 k, mul_one] at hcoord
        exact hcoord
      · intro j _ hjk
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · rw [ih j.val (hk ▸ hlt) j rfl, zero_mul]
        · rw [h2 k j hgt, mul_zero]
      · intro hk'
        exact absurd (Finset.mem_univ k) hk'
  intro k
  exact key k.val k rfl

theorem le_finrank_range_of_pivots {d n : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2))
    (x : Fin n → (Fin d → ZMod 2)) (p : Fin n → Fin d)
    (h1 : ∀ k, (A *ᵥ x k) (p k) = 1) (h2 : ∀ k j, k < j → (A *ᵥ x j) (p k) = 0) :
    n ≤ finrank (ZMod 2) (LinearMap.range A.mulVecLin) := by
  have hli := linearIndependent_of_pivots (fun k => A *ᵥ x k) p h1 h2
  have hli' : LinearIndependent (ZMod 2)
      (fun k => (⟨A *ᵥ x k, ⟨x k, rfl⟩⟩ : LinearMap.range A.mulVecLin)) :=
    LinearIndependent.of_comp (LinearMap.range A.mulVecLin).subtype hli
  simpa using hli'.fintype_card_le_finrank

theorem le_finrank_ker_of_pivots {d n : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2))
    (y : Fin n → (Fin d → ZMod 2)) (p : Fin n → Fin d) (hker : ∀ k, A *ᵥ y k = 0)
    (h1 : ∀ k, y k (p k) = 1) (h2 : ∀ k j, k < j → y j (p k) = 0) :
    n ≤ finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := by
  have hli := linearIndependent_of_pivots y p h1 h2
  have hli' : LinearIndependent (ZMod 2)
      (fun k => (⟨y k, by simpa using hker k⟩ : LinearMap.ker A.mulVecLin)) :=
    LinearIndependent.of_comp (LinearMap.ker A.mulVecLin).subtype hli
  simpa using hli'.fintype_card_le_finrank

end CFSG.LocalAnalysis.WeakClosure81
