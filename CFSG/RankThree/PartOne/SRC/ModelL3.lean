module

public import CFSG.RankThree.PartOne.SRC.Centralizer

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix

section Block

variable {F : Type*} [Field F]

@[expose] def blockMat (A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
     (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1]

theorem det_blockMat (A : SpecialLinearGroup (Fin 2) F) : (blockMat A).det = 1 := by
  have h := A.2
  rw [Matrix.det_fin_two] at h
  simp [blockMat, Matrix.det_fin_three, h]

@[expose] def blockSL (A : SpecialLinearGroup (Fin 2) F) : SpecialLinearGroup (Fin 3) F :=
  ⟨blockMat A, det_blockMat A⟩

theorem coe_blockSL (A : SpecialLinearGroup (Fin 2) F) :
    ((blockSL A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blockMat A := rfl

theorem blockSL_one : blockSL (1 : SpecialLinearGroup (Fin 2) F) = 1 := by
  ext i j
  rw [coe_blockSL]
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem blockSL_mul (A B : SpecialLinearGroup (Fin 2) F) :
    blockSL (A * B) = blockSL A * blockSL B := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL, coe_blockSL]
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

@[expose] def blockHom : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun := blockSL
  map_one' := blockSL_one
  map_mul' := blockSL_mul

theorem coe_blockHom (A : SpecialLinearGroup (Fin 2) F) :
    ((blockHom A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blockMat A := rfl

theorem blockHom_injective : Function.Injective (blockHom (F := F)) := by
  intro A B h
  have h' := congrArg (fun M : SpecialLinearGroup (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F)) h
  ext i j
  have := congrFun (congrFun h' (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [coe_blockHom, blockMat] using this

@[expose] def invol : SpecialLinearGroup (Fin 3) F :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_invol : ((invol : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl

theorem blockHom_comm_invol (A : SpecialLinearGroup (Fin 2) F) :
    blockHom A * invol = invol * blockHom A := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockHom,
    coe_invol]
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem invol_sq : (invol : SpecialLinearGroup (Fin 3) F) ^ 2 = 1 := by
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_invol]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end Block

section PSL

open scoped MatrixGroups

variable {F : Type*} [Field F]

@[expose] noncomputable def psl3Emb : SpecialLinearGroup (Fin 2) F →* PSL(3, F) :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F))).comp blockHom

theorem psl3Emb_injective : Function.Injective (psl3Emb (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [psl3Emb, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hA
  obtain ⟨r, -, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have e := fun i j => congrFun (congrFun hrA i) j
  have h22 := e 2 2
  simp [coe_blockHom, blockMat, Matrix.scalar_apply] at h22
  have hr1 : r = 1 := h22
  subst hr1
  have hA1 : (blockHom A : SpecialLinearGroup (Fin 3) F) = 1 :=
    Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one])
  exact blockHom_injective (hA1.trans (map_one blockHom).symm)

@[expose] noncomputable def psl3Invol : PSL(3, F) :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F)) invol

theorem psl3Emb_comm (A : SpecialLinearGroup (Fin 2) F) :
    psl3Emb A * psl3Invol = psl3Invol * psl3Emb A := by
  rw [psl3Emb, psl3Invol, MonoidHom.comp_apply, ← map_mul, ← map_mul, blockHom_comm_invol]

theorem orderOf_psl3Invol (h : (-1 : F) ≠ 1) : orderOf (psl3Invol : PSL(3, F)) = 2 := by
  have h2 : (psl3Invol : PSL(3, F)) ^ 2 = 1 := by
    rw [psl3Invol, ← map_pow, invol_sq, map_one]
  refine orderOf_eq_prime h2 fun h1 => ?_
  rw [psl3Invol, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  have e := fun i j => congrFun (congrFun hr i) j
  have h00 := e 0 0
  have h22 := e 2 2
  simp [coe_invol, Matrix.scalar_apply] at h00 h22
  exact h (h00.symm.trans h22)

end PSL


theorem rankFourCover_psl3 {p e : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]
    (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) (he : 4 ≤ e) :
    RankFourCover p (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq F p]; exact hp2)
  exact rankFourCover_of_SL2 hF hp2 he psl3Emb psl3Emb_injective (orderOf_psl3Invol hneg)
    psl3Emb_comm

end CFSG.RankThree.PartOne.SRC
