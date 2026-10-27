module

public import CFSG.ClassicalInvolution.WeakCT.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem trace_blockMat {F : Type*} [Field F] {m k i : ℕ} (h : i + k ≤ m)
    (A : Matrix (Fin k) (Fin k) F) :
    (blockMat m i A).trace = A.trace + (m - k : ℕ) := by
  unfold blockMat
  rw [Matrix.trace_add, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    blockSel_transpose_mul_self h, Matrix.one_mul, Matrix.trace_sub]
  simp only [Matrix.trace_one, Fintype.card_fin]
  have hk : k ≤ m := by omega
  have hmk : (m - k : ℕ) + k = m := Nat.sub_add_cancel hk
  have hcast : ((m - k : ℕ) : F) + (k : F) = (m : F) := by
    rw [← Nat.cast_add, hmk]
  linear_combination -hcast

theorem trace_blockSL {F : Type} [Field F] {m k i : ℕ} (h : i + k ≤ m)
    (A : SL(k, F)) :
    ((blockSL F m k i h A : SL(m, F)) : Matrix (Fin m) (Fin m) F).trace =
      (A : Matrix (Fin k) (Fin k) F).trace + (m - k : ℕ) :=
  trace_blockMat h _

end CFSG.LocalAnalysis.UniquenessCase.UC22
