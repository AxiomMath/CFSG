module

public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG

namespace FiveTransitive.AutSixteenPerfect

open scoped commutatorElement

abbrev GL4 := Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)

private theorem transvection_commutator_matrix :
    ∀ (i j k : Fin 4) (c : ZMod 2), i ≠ j → i ≠ k → j ≠ k →
    Matrix.transvection i k c * Matrix.transvection k j 1 *
      Matrix.transvection i k (-c) * Matrix.transvection k j (-1) =
      Matrix.transvection i j c := by
  decide

private theorem transvection_mem (i j : Fin 4) (hij : i ≠ j) (c : ZMod 2) :
    Matrix.GeneralLinearGroup.transvection i j hij c ∈ commutator GL4 := by
  have hk : ∃ k : Fin 4, i ≠ k ∧ j ≠ k := by
    revert i j
    decide
  obtain ⟨k, hik, hjk⟩ := hk
  let a := Matrix.GeneralLinearGroup.transvection i k hik c
  let b := Matrix.GeneralLinearGroup.transvection k j hjk.symm (1 : ZMod 2)
  have hcomm : ⁅a, b⁆ = Matrix.GeneralLinearGroup.transvection i j hij c := by
    apply Units.ext
    exact transvection_commutator_matrix i j k c hij hik hjk
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

private theorem diagonal_eq_one (D : Fin 4 → ZMod 2)
    (hD : (Matrix.diagonal D).det ≠ 0) : D = fun _ => 1 := by
  funext i
  have hne : D i ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
    exact hD i (Finset.mem_univ i)
  have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact hz (D i) hne

private theorem diagonal_mem (D : Fin 4 → ZMod 2)
    (hD : (Matrix.diagonal D).det ≠ 0)
    (u : GL4) (hu : (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = Matrix.diagonal D) :
    u ∈ commutator GL4 := by
  have hu1 : u = 1 := by
    apply Units.ext
    simpa only [diagonal_eq_one D hD, Matrix.diagonal_one, Units.val_one] using hu
  rw [hu1]
  exact Subgroup.one_mem _

private theorem matrix_mem (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M.det ≠ 0) :
    ∀ u : GL4, (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M → u ∈ commutator GL4 := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : GL4, (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M →
      u ∈ commutator GL4) M hM
  · exact diagonal_mem
  · intro t u hu
    have heq : u = Matrix.GeneralLinearGroup.transvection t.i t.j t.hij t.c := by
      apply Units.ext
      exact hu
    rw [heq]
    exact transvection_mem t.i t.j t.hij t.c
  · intro A B hA hB hPA hPB u hu
    let a := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
    let b := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
    have heq : u = a * b := by
      apply Units.ext
      exact hu
    rw [heq]
    exact Subgroup.mul_mem _ (hPA a rfl) (hPB b rfl)

theorem perfect : Group.IsPerfect GL4 := by
  rw [Group.isPerfect_def]
  apply top_unique
  intro g _
  exact matrix_mem _ (Matrix.GeneralLinearGroup.det_ne_zero g) g rfl

theorem card : Nat.card GL4 = 20160 := by
  have h := Matrix.card_GL_field (𝔽 := ZMod 2) 4
  norm_num [Fin.prod_univ_succ] at h
  simpa only [Nat.card_eq_fintype_card] using h

end FiveTransitive.AutSixteenPerfect

end CFSG
