module

public import CFSG.RankThree.PartOne.LIT.FiveRecords
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix LinearMap

theorem exists_diagonal_congr {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : Mᵀ = M) :
    ∃ (g : GL (Fin n) K) (d : Fin n → K),
      (g : Matrix (Fin n) (Fin n) K)ᵀ * M * (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := by
  classical
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hsymm : LinearMap.IsSymm (Matrix.toBilin' M) := by
    refine ⟨fun x y => ?_⟩
    simp only [Matrix.toBilin'_apply', RingHom.id_apply]
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (V := Fin n → K) (K := K)
    (B := Matrix.toBilin' M) hsymm
  let v' := v.reindex (finCongr (Module.finrank_fin_fun K))
  have hv' : ∀ i j, i ≠ j → Matrix.toBilin' M (v' i) (v' j) = 0 := by
    intro i j hij
    have := hv (i := (finCongr (Module.finrank_fin_fun K)).symm i)
      (j := (finCongr (Module.finrank_fin_fun K)).symm j) (by simpa using hij)
    simpa [v'] using this
  have hinv : Invertible ((Pi.basisFun K (Fin n)).toMatrix v') :=
    (Pi.basisFun K (Fin n)).invertibleToMatrix v'
  let g : GL (Fin n) K := ⟨_, _, hinv.mul_invOf_self, hinv.invOf_mul_self⟩
  refine ⟨g, fun i => Matrix.toBilin' M (v' i) (v' i), ?_⟩
  ext i j
  have hg : (g : Matrix (Fin n) (Fin n) K) = Matrix.of fun a b => v' b a := by
    ext a b
    simp [g, Module.Basis.toMatrix_apply]
  rw [hg]
  have key : ((Matrix.of fun a b => v' b a)ᵀ * M * (Matrix.of fun a b => v' b a)) i j =
      Matrix.toBilin' M (v' i) (v' j) := by
    simp only [Matrix.toBilin'_apply', Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      dotProduct, Matrix.mulVec]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [key]
  by_cases hij : i = j
  · subst hij; simp
  · rw [hv' i j hij, Matrix.diagonal_apply_ne _ hij]


theorem diag_cong_table : ∀ a₁ a₂ a₃ : ZMod 5, (a₁ = 1 ∨ a₁ = 2) → (a₂ = 1 ∨ a₂ = 2) →
    (a₃ = 1 ∨ a₃ = 2) → ∃ (h : M3) (c : ZMod 5), h.det ≠ 0 ∧ c ≠ 0 ∧
      hᵀ * diagonal ![a₁, a₂, a₃] * h = c • 1 := by
  intro a₁ a₂ a₃ h₁ h₂ h₃
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> rcases h₃ with rfl | rfl
  · exact ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], 1, by decide, by decide, by decide⟩
  · exact ⟨!![0, 1, 1; 0, 1, 4; 1, 0, 0], 2, by decide, by decide, by decide⟩
  · exact ⟨!![0, 1, 1; 1, 0, 0; 0, 1, 4], 2, by decide, by decide, by decide⟩
  · exact ⟨!![0, 0, 1; 2, 2, 0; 2, 3, 0], 1, by decide, by decide, by decide⟩
  · exact ⟨!![0, 0, 1; 1, 1, 0; 1, 4, 0], 2, by decide, by decide, by decide⟩
  · exact ⟨!![0, 2, 2; 1, 0, 0; 0, 2, 3], 1, by decide, by decide, by decide⟩
  · exact ⟨!![0, 2, 2; 0, 2, 3; 1, 0, 0], 1, by decide, by decide, by decide⟩
  · exact ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], 2, by decide, by decide, by decide⟩

@[expose] def scaleFive (x : ZMod 5) : ZMod 5 := if x = 1 ∨ x = 2 then 1 else 2

theorem scaleFive_ne_zero : ∀ x : ZMod 5, scaleFive x ≠ 0 := by decide

theorem scaleFive_sq_mul : ∀ x : ZMod 5, x ≠ 0 →
    scaleFive x ^ 2 * x = 1 ∨ scaleFive x ^ 2 * x = 2 := by decide

theorem exists_congr_scalar_five (M : M3) (hM : Mᵀ = M) (hdet : M.det ≠ 0) :
    ∃ (g : GL (Fin 3) (ZMod 5)) (c : ZMod 5), c ≠ 0 ∧
      (g : M3)ᵀ * M * (g : M3) = c • 1 := by
  obtain ⟨g₀, d, hd⟩ := exists_diagonal_congr (by decide : (2 : ZMod 5) ≠ 0) M hM
  have hg₀ : (g₀ : M3).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (g₀ : M3)).mp g₀.isUnit).ne_zero
  have hdiag : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hd, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hg₀ hdet) hg₀
  rw [det_diagonal] at hdiag
  have hd0 : ∀ i, d i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mp hdiag i (Finset.mem_univ i)
  set s : Fin 3 → ZMod 5 := fun i => scaleFive (d i) with hs
  have hsdet : (Matrix.diagonal s).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => scaleFive_ne_zero _
  set a : Fin 3 → ZMod 5 := fun i => s i ^ 2 * d i with ha
  have hdiag2 : (Matrix.diagonal s)ᵀ * Matrix.diagonal d * Matrix.diagonal s =
      Matrix.diagonal a := by
    rw [diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    simp only [ha]
    ring
  have hadiag : Matrix.diagonal a = Matrix.diagonal ![a 0, a 1, a 2] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨h, c, hh, hc, hhc⟩ := diag_cong_table (a 0) (a 1) (a 2)
    (scaleFive_sq_mul _ (hd0 0)) (scaleFive_sq_mul _ (hd0 1)) (scaleFive_sq_mul _ (hd0 2))
  refine ⟨g₀ * GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal s) hsdet *
    GeneralLinearGroup.mkOfDetNeZero h hh, c, hc, ?_⟩
  rw [← hhc, ← hadiag, ← hdiag2, ← hd]
  simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]
  rfl

end CFSG.RankThree.PartOne.LIT
