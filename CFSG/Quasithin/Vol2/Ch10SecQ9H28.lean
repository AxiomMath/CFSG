module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H16

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

@[expose] def blk (A : Matrix (Fin m) (Fin m) (ZMod 2)) (B : Matrix (Fin k) (Fin k) (ZMod 2)) :
    Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

variable (A : Matrix (Fin m) (Fin m) (ZMod 2)) (B : Matrix (Fin k) (Fin k) (ZMod 2))

theorem blk_cc (a c : Fin m) : blk A B (Fin.castAdd k a) (Fin.castAdd k c) = A a c := by
  simp [blk, reindex_apply]

theorem blk_cn (a : Fin m) (d : Fin k) : blk A B (Fin.castAdd k a) (Fin.natAdd m d) = 0 := by
  simp [blk, reindex_apply]

theorem blk_nc (b : Fin k) (c : Fin m) : blk A B (Fin.natAdd m b) (Fin.castAdd k c) = 0 := by
  simp [blk, reindex_apply]

theorem blk_nn (b d : Fin k) : blk A B (Fin.natAdd m b) (Fin.natAdd m d) = B b d := by
  simp [blk, reindex_apply]

theorem det_blk : (blk A B).det = A.det * B.det := by
  rw [blk, det_reindex_self, det_fromBlocks_zero₂₁]

theorem presStd_blk : PresStd (blk A B) := fun i j => blk_nc A B i j

theorem topB_blk : topB (blk A B) = A := by
  ext a c
  exact blk_cc A B a c

theorem botB_blk : botB (blk A B) = B := by
  ext b d
  exact blk_nn A B b d

theorem fin_add_cases (i : Fin (m + k)) :
    (∃ a : Fin m, i = Fin.castAdd k a) ∨ ∃ b : Fin k, i = Fin.natAdd m b := by
  rcases lt_or_ge (i : ℕ) m with h | h
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨(i : ℕ) - m, by omega⟩, Fin.ext (by simp; omega)⟩

theorem isUniTri_blk {A : Matrix (Fin m) (Fin m) (ZMod 2)} {B : Matrix (Fin k) (Fin k) (ZMod 2)}
    (hA : IsUniTri A) (hB : IsUniTri B) : IsUniTri (blk A B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;>
      rcases fin_add_cases j with ⟨c, rfl⟩ | ⟨d, rfl⟩
    · rw [blk_cc]
      refine hA.1 ?_
      rw [Fin.lt_def] at hij ⊢
      simpa using hij
    · exact blk_cn A B a d
    · exact blk_nc A B b c
    · rw [blk_nn]
      refine hB.1 ?_
      rw [Fin.lt_def] at hij ⊢
      simpa using hij
  · rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [blk_cc]
      exact hA.2 a
    · rw [blk_nn]
      exact hB.2 b

@[expose] def blkSL (A : Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (B : Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) :
    Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2) :=
  ⟨blk A B, by rw [det_blk, A.2, B.2, one_mul]⟩

theorem blkSL_mem (A : Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (B : Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) : blkSL A B ∈ stabStd m k :=
  presStd_blk _ _

theorem topH_blkSL (A : Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (B : Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) : topH m k ⟨blkSL A B, blkSL_mem A B⟩ = A :=
  Subtype.ext (topB_blk _ _)

theorem botH_blkSL (A : Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (B : Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) : botH m k ⟨blkSL A B, blkSL_mem A B⟩ = B :=
  Subtype.ext (botB_blk _ _)

theorem blkSL_mem_uniSL {A : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)}
    {B : Matrix.SpecialLinearGroup (Fin k) (ZMod 2)} (hA : A ∈ uniSL m) (hB : B ∈ uniSL k) :
    blkSL A B ∈ uniSL (m + k) :=
  isUniTri_blk hA hB

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
