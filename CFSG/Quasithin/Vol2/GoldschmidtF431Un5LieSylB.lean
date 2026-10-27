module

public import CFSG.LocalAnalysis.EvenBN.U5.Model

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem syl_mat_comm {g : hypSU h 2 1} (hg : g * z₂SU h = z₂SU h * g) :
    mat g * oddUni h 0 !![0, 1; 1, 0] = oddUni h 0 !![0, 1; 1, 0] * mat g := by
  have := congrArg mat hg
  rw [mat_mul, mat_mul, z₂SU, mat_vSU] at this
  exact this

theorem syl_comm_z_e {g : hypSU h 2 1} (hg : g * z₂SU h = z₂SU h * g) (i : Fin 2) :
    mat g (.inr (.inl 0)) (.inl i) = 0 := by
  have hm := syl_mat_comm hg
  fin_cases i
  · have := congrFun (congrFun hm (.inr (.inl 0))) (.inr (.inr 1))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this
  · have := congrFun (congrFun hm (.inr (.inl 0))) (.inr (.inr 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this

theorem syl_comm_f_e {g : hypSU h 2 1} (hg : g * z₂SU h = z₂SU h * g) (j i : Fin 2) :
    mat g (.inr (.inr j)) (.inl i) = 0 := by
  have hm := syl_mat_comm hg
  fin_cases i <;> fin_cases j
  · have := congrFun (congrFun hm (.inr (.inr 0))) (.inr (.inr 1))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this
  · have := congrFun (congrFun hm (.inr (.inr 1))) (.inr (.inr 1))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this
  · have := congrFun (congrFun hm (.inr (.inr 0))) (.inr (.inr 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this
  · have := congrFun (congrFun hm (.inr (.inr 1))) (.inr (.inr 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this

theorem syl_comm_f_z {g : hypSU h 2 1} (hg : g * z₂SU h = z₂SU h * g) (j : Fin 2) :
    mat g (.inr (.inr j)) (.inr (.inl 0)) = 0 := by
  have hm := syl_mat_comm hg
  fin_cases j
  · have := congrFun (congrFun hm (.inl 1)) (.inr (.inl 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this
  · have := congrFun (congrFun hm (.inl 0)) (.inr (.inl 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni] at this
    exact this

theorem syl_comm_AJ {g : hypSU h 2 1} (hg : g * z₂SU h = z₂SU h * g) :
    blkA (mat g) * !![0, 1; 1, 0] = !![0, 1; 1, 0] * blkD (mat g) := by
  have hm := syl_mat_comm hg
  ext i j
  have := congrFun (congrFun hm (.inl i)) (.inr (.inr j))
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni, blkA, blkD,
      Matrix.one_apply] at this ⊢ <;> linear_combination this

end CFSG.Quasithin.H13.F431.Un.L5
