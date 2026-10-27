module

public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Block

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

variable {m : ℕ}

theorem dualGLn_stabGL_mulVec_zero {A : GL (Fin (m + 1)) (ZMod 2)} (hA : A ∈ stabGL m)
    (b : Fin (m + 1) → ZMod 2) :
    (((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
      b) 0 = b 0 := by
  have hinv := mem_stabGL_iff.mp ((stabGL m).inv_mem hA)
  have hval : ((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) =
      ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))ᵀ := rfl
  rw [hval]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, col_zero_zero_of_mulVec hinv,
    col_succ_zero_of_mulVec hinv, -Matrix.coe_units_inv]

theorem dualGLn_stabGL_mulVec_succ {A : GL (Fin (m + 1)) (ZMod 2)} (hA : A ∈ stabGL m)
    (b : Fin (m + 1) → ZMod 2) (i : Fin m) :
    (((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
        b) i.succ =
      (((dualGLn m (blockHom m ⟨A, hA⟩) : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ
        fun j : Fin m => b j.succ) i +
        ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 i.succ *
          b 0 := by
  have hval : ∀ {k : ℕ} (g : GL (Fin k) (ZMod 2)), ((dualGLn k g : GL (Fin k) (ZMod 2)) :
      Matrix (Fin k) (Fin k) (ZMod 2)) = ((g⁻¹ : GL (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2))ᵀ :=
    fun g => rfl
  have hb : (((blockHom m ⟨A, hA⟩)⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      blk ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) := by
    rw [← map_inv]
    rfl
  rw [hval, hval, hb]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_comm, -Matrix.coe_units_inv]

end CFSG.ASVolI.ChH.VectorStabilizer
