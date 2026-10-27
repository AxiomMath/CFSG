module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix

section Block4

variable {F : Type*} [Field F]

@[expose] def blockMat4 (A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0, 0;
     (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0, 0;
     0, 0, 1, 0; 0, 0, 0, 1]

theorem det_blockMat4 (A : SpecialLinearGroup (Fin 2) F) : (blockMat4 A).det = 1 := by
  have h := A.2
  rw [Matrix.det_fin_two] at h
  simp [blockMat4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination h

@[expose] def blockSL4 (A : SpecialLinearGroup (Fin 2) F) : SpecialLinearGroup (Fin 4) F :=
  ⟨blockMat4 A, det_blockMat4 A⟩

theorem coe_blockSL4 (A : SpecialLinearGroup (Fin 2) F) :
    ((blockSL4 A : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blockMat4 A := rfl

theorem blockSL4_one : blockSL4 (1 : SpecialLinearGroup (Fin 2) F) = 1 := by
  ext i j
  rw [coe_blockSL4]
  fin_cases i <;> fin_cases j <;> simp [blockMat4]

theorem blockSL4_mul (A B : SpecialLinearGroup (Fin 2) F) :
    blockSL4 (A * B) = blockSL4 A * blockSL4 B := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL4, coe_blockSL4, coe_blockSL4]
  fin_cases i <;> fin_cases j <;>
    simp [blockMat4, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

@[expose] def blockHom4 : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 4) F where
  toFun := blockSL4
  map_one' := blockSL4_one
  map_mul' := blockSL4_mul

theorem coe_blockHom4 (A : SpecialLinearGroup (Fin 2) F) :
    ((blockHom4 A : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blockMat4 A := rfl

theorem blockHom4_injective : Function.Injective (blockHom4 (F := F)) := by
  intro A B h
  have h' := congrArg (fun M : SpecialLinearGroup (Fin 4) F => (M : Matrix (Fin 4) (Fin 4) F)) h
  ext i j
  have := congrFun (congrFun h' (Fin.castSucc (Fin.castSucc i))) (Fin.castSucc (Fin.castSucc j))
  fin_cases i <;> fin_cases j <;> simpa [coe_blockHom4, blockMat4] using this

@[expose] def invol4 : SpecialLinearGroup (Fin 4) F :=
  ⟨!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]⟩

theorem coe_invol4 : ((invol4 : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := rfl

theorem invol4_sq : (invol4 : SpecialLinearGroup (Fin 4) F) ^ 2 = 1 := by
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_invol4]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

end Block4

section PSL4

open scoped MatrixGroups

variable {F : Type*} [Field F]

@[expose] noncomputable def psl4Emb : SpecialLinearGroup (Fin 2) F →* PSL(4, F) :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 4) F))).comp blockHom4

@[expose] noncomputable def psl4Invol : PSL(4, F) :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 4) F)) invol4

theorem orderOf_psl4Invol (h : (-1 : F) ≠ 1) : orderOf (psl4Invol : PSL(4, F)) = 2 := by
  have h2 : (psl4Invol : PSL(4, F)) ^ 2 = 1 := by
    rw [psl4Invol, ← map_pow, invol4_sq, map_one]
  refine orderOf_eq_prime h2 fun h1 => ?_
  rw [psl4Invol, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  have e := fun i j => congrFun (congrFun hr i) j
  have h00 := e 0 0
  have h22 := e 2 2
  simp [coe_invol4, Matrix.scalar_apply] at h00 h22
  exact h (h00.symm.trans h22)

end PSL4

end CFSG.RankThree.PartOne.SRC
