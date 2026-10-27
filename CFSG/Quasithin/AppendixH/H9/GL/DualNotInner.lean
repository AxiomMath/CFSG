module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.GL

private theorem dualGLn_transvection {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ((dualGLn n (Matrix.GeneralLinearGroup.transvection i j hij 1) : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + Matrix.single j i 1 := by
  show ((((Matrix.GeneralLinearGroup.transvection i j hij 1)⁻¹ : GL (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ = _
  have hinv : (Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2))⁻¹ =
      Matrix.GeneralLinearGroup.transvection i j hij (-1 : ZMod 2) := rfl
  have hneg : (-1 : ZMod 2) = 1 := by decide
  rw [hinv, hneg]
  show (Matrix.transvection i j (1 : ZMod 2))ᵀ = _
  rw [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

theorem dualGLn_not_inner_aux {n : ℕ} (hn : 3 ≤ n) :
    ¬ ∃ B : GL (Fin n) (ZMod 2), ∀ X : GL (Fin n) (ZMod 2), dualGLn n X = B * X * B⁻¹ := by
  rintro ⟨B, hB⟩
  have key : ∀ i j : Fin n, i ≠ j → ∀ a : Fin n, a ≠ j →
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) a i = 0 := by
    intro i j hij a haj
    have h1 := hB (Matrix.GeneralLinearGroup.transvection i j hij 1)
    have h2 : dualGLn n (Matrix.GeneralLinearGroup.transvection i j hij 1) * B =
        B * Matrix.GeneralLinearGroup.transvection i j hij 1 := by
      rw [h1, mul_assoc, inv_mul_cancel, mul_one]
    have hval : ((Matrix.GeneralLinearGroup.transvection i j hij 1 : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + Matrix.single i j 1 := rfl
    have h3 := congrArg
      (fun Y : GL (Fin n) (ZMod 2) => (Y : Matrix (Fin n) (Fin n) (ZMod 2)) a j) h2
    simp only [Units.val_mul, dualGLn_transvection, hval,
      Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_apply, Matrix.single_mul_apply_of_ne _ j i a j haj,
      Matrix.mul_single_apply_same] at h3
    simpa using h3.symm
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hcol : ∀ a : Fin n, (B : Matrix (Fin n) (Fin n) (ZMod 2)) a ⟨0, by omega⟩ = 0 := by
    intro a
    by_cases ha : a = ⟨1, by omega⟩
    · exact key _ _ h02 a (by rw [ha]; exact h12)
    · exact key _ _ h01 a ha
  have h0 : ((B⁻¹ * B : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
      ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply] at h0
  simp [hcol] at h0

end CFSG.ASVolI.ChH.GL
