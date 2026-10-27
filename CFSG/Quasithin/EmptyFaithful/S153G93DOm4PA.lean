module

import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.S153G93D.Om4P

open Matrix

variable {F : Type} [Field F]

@[expose] def defect (A B : Matrix (Fin 2) (Fin 2) F) (τ : F ≃+* F)
    (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  A * X.map τ * Bᵀ - X

@[expose] def rk1 (x y : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => x i * y j

@[expose] def cross (A : Matrix (Fin 2) (Fin 2) F) (τ : F ≃+* F) (x : Fin 2 → F) : F :=
  (A *ᵥ fun k => τ (x k)) 0 * x 1 - (A *ᵥ fun k => τ (x k)) 1 * x 0

theorem defect_rk1_apply (A B : Matrix (Fin 2) (Fin 2) F) (τ : F ≃+* F) (x y : Fin 2 → F)
    (i j : Fin 2) :
    defect A B τ (rk1 x y) i j =
      (A *ᵥ fun k => τ (x k)) i * (B *ᵥ fun k => τ (y k)) j - x i * y j := by
  simp only [defect, rk1, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_mul]
  ring

theorem cross_apply (A : Matrix (Fin 2) (Fin 2) F) (τ : F ≃+* F) (x : Fin 2 → F) :
    cross A τ x = (A 0 0 * τ (x 0) + A 0 1 * τ (x 1)) * x 1 -
      (A 1 0 * τ (x 0) + A 1 1 * τ (x 1)) * x 0 := by
  simp only [cross, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem injective_defect_rk1 (A B : Matrix (Fin 2) (Fin 2) F) (τ : F ≃+* F) {x : Fin 2 → F}
    (hx : cross A τ x ≠ 0) :
    Function.Injective fun y : Fin 2 → F => defect A B τ (rk1 x y) := by
  intro y y' h
  funext j
  have h' : defect A B τ (rk1 x y) = defect A B τ (rk1 x y') := h
  have h0 := congrFun (congrFun h' 0) j
  have h1 := congrFun (congrFun h' 1) j
  rw [defect_rk1_apply, defect_rk1_apply] at h0 h1
  have key : cross A τ x * (y j - y' j) = 0 := by
    unfold cross
    linear_combination (-(A *ᵥ fun k => τ (x k)) 0) * h1 + ((A *ᵥ fun k => τ (x k)) 1) * h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hx)

theorem exists_cross_ne_zero {A : Matrix (Fin 2) (Fin 2) F} (hA : A ≠ 0) {τ : F ≃+* F}
    (h : ¬ (τ = 1 ∧ ∃ p : F, A = p • 1)) : ∃ x : Fin 2 → F, cross A τ x ≠ 0 := by
  by_contra hcon0
  have hcon : ∀ x : Fin 2 → F, cross A τ x = 0 := fun x => by
    by_contra hx
    exact hcon0 ⟨x, hx⟩
  have e10 : A 1 0 = 0 := by
    have := hcon ![1, 0]
    rw [cross_apply] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one,
      map_zero] at this
    linear_combination (-1 : F) * this
  have e01 : A 0 1 = 0 := by
    have := hcon ![0, 1]
    rw [cross_apply] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one,
      map_zero] at this
    linear_combination this
  have e11 : A 0 0 = A 1 1 := by
    have := hcon ![1, 1]
    rw [cross_apply] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one] at this
    linear_combination this - e01 + e10
  have hAp : A = A 0 0 • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10, e01, e11]
  have hp : A 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hAp
    exact hA hAp
  have hτ : τ = 1 := by
    ext ω
    have := hcon ![1, ω]
    rw [cross_apply] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one] at this
    have h2 : A 0 0 * (ω - τ ω) = 0 := by
      linear_combination this - (ω * τ ω) * e01 + e10 - (τ ω) * e11
    have h3 := (mul_eq_zero.mp h2).resolve_left hp
    exact (sub_eq_zero.mp h3).symm
  exact h ⟨hτ, A 0 0, hAp⟩

theorem exists_injective_defect {A B : Matrix (Fin 2) (Fin 2) F} (hA : A ≠ 0) (hB : B ≠ 0)
    {τ : F ≃+* F} (h : ¬ (τ = 1 ∧ (∃ p : F, A = p • 1) ∧ ∃ m : F, B = m • 1)) :
    ∃ ψ : (Fin 2 → F) → Matrix (Fin 2) (Fin 2) F,
      Function.Injective fun y => defect A B τ (ψ y) := by
  by_cases hTA : ∃ x : Fin 2 → F, cross A τ x ≠ 0
  · obtain ⟨x, hx⟩ := hTA
    exact ⟨rk1 x, injective_defect_rk1 A B τ hx⟩
  · have hA' : τ = 1 ∧ ∃ p : F, A = p • 1 := by
      by_contra hcon
      exact hTA (exists_cross_ne_zero hA hcon)
    by_cases hTB : ∃ x : Fin 2 → F, cross B τ x ≠ 0
    · obtain ⟨x, hx⟩ := hTB
      have hinj := injective_defect_rk1 B A τ (x := x) hx
      refine ⟨fun y => (rk1 x y)ᵀ, ?_⟩
      have key : ∀ X : Matrix (Fin 2) (Fin 2) F,
          defect A B τ Xᵀ = (defect B A τ X)ᵀ := by
        intro X
        simp only [defect, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_map,
          Matrix.transpose_transpose, Matrix.mul_assoc]
      intro y y' hyy
      apply hinj
      have := congrArg Matrix.transpose hyy
      simp only [key, Matrix.transpose_transpose] at this
      exact this
    · have hB' : τ = 1 ∧ ∃ m : F, B = m • 1 := by
        by_contra hcon
        exact hTB (exists_cross_ne_zero hB hcon)
      exact absurd ⟨hA'.1, hA'.2, hB'.2⟩ h

end CFSG.Quasithin.S153G93D.Om4P
