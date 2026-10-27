module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import CFSG.LocalAnalysis.ZStar.PadicTrace

public section

namespace CFSG

namespace ZStar.FixedPointFreeTrace

universe u

variable {α : Type u}

@[expose] noncomputable def involutionMatrix
    (f : α → α) (hf : Function.Involutive f) :
    Matrix α α ℤ_[2] := by
  classical
  exact (hf.toPerm f).permMatrix ℤ_[2]

private def pairEquiv [LinearOrder α]
    (f : α → α) (hf : Function.Involutive f)
    (hfree : ∀ i, f i ≠ i) :
    {i : α // i < f i} ⊕ {i : α // i < f i} ≃ α where
  toFun x := x.elim
    (fun i : {i : α // i < f i} => (i : α))
    (fun i : {i : α // i < f i} => f i)
  invFun i := if h : i < f i then
      Sum.inl ⟨i, h⟩
    else
      Sum.inr ⟨f i, by
        have hle : f i ≤ i := le_of_not_gt h
        have hlt : f i < i := lt_of_le_of_ne hle (hfree i)
        simpa only [hf i] using hlt⟩
  left_inv x := by
    cases x with
    | inl i => simp [i.property]
    | inr i =>
        have hnot : ¬f i < f (f i) := by
          simpa only [hf i] using not_lt_of_ge (le_of_lt i.property)
        dsimp only [Sum.elim_inr]
        rw [dite_eq_right hnot]
        congr 1
        apply Subtype.ext
        exact hf i
  right_inv i := by
    by_cases h : i < f i
    · simp [h]
    · simp [h, hf i]

theorem trace_mul_involutionMatrix_eq_zero
    [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Function.Involutive f)
    (hfree : ∀ i, f i ≠ i)
    (E : Matrix α α ℤ_[2])
    (hidem : E * E = E)
    (hinv : ∀ i j, E (f i) (f j) = E i j) :
    Matrix.trace (E * involutionMatrix f hf) = 0 := by
  let _ : LinearOrder α :=
    LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  let κ := {i : α // i < f i}
  let e : κ ⊕ κ ≃ α := pairEquiv f hf hfree
  let P : Matrix κ κ ℤ_[2] := fun i j => E i j
  let Q : Matrix κ κ ℤ_[2] := fun i j => E i (f j)
  have hsum (a b : κ) :
      (∑ x : α, E a x * E x (f b)) =
        (∑ r : κ, E a r * E r (f b)) +
        (∑ r : κ, E a (f r) * E (f r) (f b)) := by
    calc
      (∑ x : α, E a x * E x (f b)) =
          ∑ x : κ ⊕ κ, E a (e x) * E (e x) (f b) := by
        symm
        apply Fintype.sum_equiv e
        intro x
        rfl
      _ = (∑ r : κ, E a (e (Sum.inl r)) * E (e (Sum.inl r)) (f b)) +
          ∑ r : κ, E a (e (Sum.inr r)) * E (e (Sum.inr r)) (f b) :=
        Fintype.sum_sum_type _
      _ = (∑ r : κ, E a r * E r (f b)) +
          (∑ r : κ, E a (f r) * E (f r) (f b)) := by rfl
  have hoff : P * Q + Q * P = Q := by
    refine Matrix.ext fun a b => ?_
    have hentry := congrArg (fun M : Matrix α α ℤ_[2] => M a (f b)) hidem
    rw [Matrix.mul_apply, hsum a b] at hentry
    change
      (∑ r : κ, E a r * E r (f b)) +
          (∑ r : κ, E a (f r) * E r b) = E a (f b)
    simpa only [hinv] using hentry
  have htraceQ : Matrix.trace Q = 0 :=
    ZStar.PadicTrace.trace_eq_zero_of_mul_add_mul_eq P Q hoff
  have hdiag (i : α) :
      (E * involutionMatrix f hf) i i = E i (f i) := by
    unfold involutionMatrix
    change Matrix.vecMul (E i) _ i = E i (f i)
    rw [@Matrix.vecMul_permMatrix α ℤ_[2] (Classical.decEq α)
      (hf.toPerm f) _ (E i) _]
    rw [hf.toPerm_symm]
    rfl
  change (∑ i : α, (E * involutionMatrix f hf) i i) = 0
  simp_rw [hdiag]
  calc
    (∑ i : α, E i (f i)) =
        ∑ x : κ ⊕ κ, E (e x) (f (e x)) := by
      symm
      apply Fintype.sum_equiv e
      intro x
      rfl
    _ = (∑ r : κ, E (e (Sum.inl r)) (f (e (Sum.inl r)))) +
        ∑ r : κ, E (e (Sum.inr r)) (f (e (Sum.inr r))) :=
      Fintype.sum_sum_type _
    _ = (∑ r : κ, E r (f r)) +
        ∑ r : κ, E (f r) (f (f r)) := by rfl
    _ = Matrix.trace Q + Matrix.trace Q := by
      simp only [hinv]
      rfl
    _ = 0 := by rw [htraceQ, zero_add]

end ZStar.FixedPointFreeTrace

end CFSG
