module

public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.StandardType

private def ggPDTranslate {V : Type*} [Add V] (a : V) (X : Set V) : Set V :=
  (fun y => y + a) '' X

private theorem ggPDTranslate_zero {V : Type*} [AddZeroClass V] (X : Set V) :
    ggPDTranslate 0 X = X := by
  unfold ggPDTranslate
  ext z
  simp

private theorem ggPDTranslate_add {V : Type*} [AddSemigroup V] (a b : V) (X : Set V) :
    ggPDTranslate a (ggPDTranslate b X) = ggPDTranslate (b + a) X := by
  unfold ggPDTranslate
  rw [Set.image_image]
  congr 1
  funext x
  rw [add_assoc]

private theorem ggPDTranslate_neg {V : Type*} [AddCommGroup V] (a : V) (X : Set V) :
    (fun x : V => -x) '' ggPDTranslate a X
      = ggPDTranslate (-a) ((fun x : V => -x) '' X) := by
  unfold ggPDTranslate
  rw [Set.image_image]
  rw [Set.image_image]
  congr 1
  funext x
  exact neg_add x a

theorem ggPD_symm_support
    {V : Type*} [AddCommGroup V]
    (h3 : ∀ x : V, (3 : ℕ) • x = 0)
    (L : V →+ V) (S : Set V) (t : V)
    (hneg : (fun x => -x) '' S = S)
    (haff : (fun x => L x + t) '' S = S) :
    L '' S = S := by
  classical
  set U : Set V := L '' S with hU
  have hUneg : (fun x : V => -x) '' U = U := by
    rw [hU, Set.image_image]
    rw [show (fun x : V => - (L x)) = (fun x : V => L (-x)) from by
          funext x; exact (map_neg L x).symm]
    rw [← Set.image_image, hneg]
  have hUt : ggPDTranslate t U = S := by
    unfold ggPDTranslate
    rw [hU, Set.image_image]
    exact haff
  have hUm : ggPDTranslate (-t) U = S := by
    rw [← hUneg, ← ggPDTranslate_neg t U, hUt, hneg]
  have hU2 : ggPDTranslate (t + t) U = U := by
    have h := congrArg (ggPDTranslate t) (hUt.trans hUm.symm)
    rw [ggPDTranslate_add] at h
    rw [ggPDTranslate_add] at h
    simpa [ggPDTranslate_zero] using h
  have hU1 : ggPDTranslate t U = U := by
    have h := congrArg (ggPDTranslate t) hU2
    rw [ggPDTranslate_add] at h
    have h3t : (t + t) + t = 0 := by
      rw [add_assoc, ← three_nsmul]
      exact h3 t
    simpa [h3t, ggPDTranslate_zero] using h.symm
  rw [← hUt, hU1, hU]

end CFSG.StandardType

end
