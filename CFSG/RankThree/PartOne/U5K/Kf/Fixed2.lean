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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix

variable {K : Type} [Field K] [CharP K 2] {n : Type} [Fintype n] [DecidableEq n]

theorem exists_common_fixed (S : Finset (Matrix n n K))
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) (hsq : ∀ A ∈ S, A * A = 1)
    (W : Submodule K (n → K)) (hW : W ≠ ⊥) (hinv : ∀ A ∈ S, ∀ w ∈ W, A *ᵥ w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ A ∈ S, A *ᵥ w = w := by
  classical
  induction S using Finset.induction_on generalizing W with
  | empty =>
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨w, hw, hw0, by simp⟩
  | insert A S hA ih =>
    let W₁ : Submodule K (n → K) :=
      { carrier := {w | w ∈ W ∧ A *ᵥ w = w}
        add_mem' := by
          rintro x y ⟨hxW, hx⟩ ⟨hyW, hy⟩
          exact ⟨W.add_mem hxW hyW, by rw [Matrix.mulVec_add, hx, hy]⟩
        zero_mem' := ⟨W.zero_mem, by simp⟩
        smul_mem' := by
          rintro c x ⟨hxW, hx⟩
          exact ⟨W.smul_mem c hxW, by rw [Matrix.mulVec_smul, hx]⟩ }
    have hAS : A ∈ insert A S := Finset.mem_insert_self A S
    have hW₁ : W₁ ≠ ⊥ := by
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      have hAw : A *ᵥ w ∈ W := hinv A hAS w hw
      have hu : A *ᵥ w - w ∈ W := W.sub_mem hAw hw
      have hA2 : A *ᵥ (A *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, hsq A hAS, Matrix.one_mulVec]
      by_cases h0 : A *ᵥ w - w = 0
      · refine (Submodule.ne_bot_iff _).2 ⟨w, ⟨hw, ?_⟩, hw0⟩
        exact sub_eq_zero.1 h0
      · refine (Submodule.ne_bot_iff _).2 ⟨A *ᵥ w - w, ⟨hu, ?_⟩, h0⟩
        rw [Matrix.mulVec_sub, hA2]
        have : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have h2 : A *ᵥ w - w = w - A *ᵥ w := by
          funext i
          simp only [Pi.sub_apply]
          linear_combination ((A *ᵥ w) i - w i) * this
        exact h2.symm
    obtain ⟨w, hwW₁, hw0, hwS⟩ := ih (fun B hB C hC => hcomm B (Finset.mem_insert_of_mem hB) C
      (Finset.mem_insert_of_mem hC)) (fun B hB => hsq B (Finset.mem_insert_of_mem hB)) W₁ hW₁
      (by
        intro B hB x hx
        obtain ⟨hxW, hxA⟩ := hx
        refine ⟨hinv B (Finset.mem_insert_of_mem hB) x hxW, ?_⟩
        rw [Matrix.mulVec_mulVec, hcomm A hAS B (Finset.mem_insert_of_mem hB),
          ← Matrix.mulVec_mulVec, hxA])
    refine ⟨w, hwW₁.1, hw0, fun B hB => ?_⟩
    rcases Finset.mem_insert.1 hB with rfl | hB'
    · exact hwW₁.2
    · exact hwS B hB'

end CFSG.RankThree.PartOne.U5K.Kf
