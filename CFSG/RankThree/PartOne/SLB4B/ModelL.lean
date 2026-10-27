module

public import CFSG.RankThree.PartOne.SLB4B.Cover

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Matrix
open scoped MatrixGroups

section Block

variable {F : Type*} [Field F] {m : ℕ}

@[expose] def blockMat (A : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin (4 + m)) (Fin (4 + m)) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv (Matrix.fromBlocks A 0 0 1)

theorem blockMat_mul (A B : Matrix (Fin 4) (Fin 4) F) :
    (blockMat (m := m) (A * B)) = blockMat A * blockMat B := by
  unfold blockMat
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem blockMat_one : blockMat (m := m) (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  unfold blockMat
  rw [Matrix.fromBlocks_one, map_one]

theorem det_blockMat (A : Matrix (Fin 4) (Fin 4) F) : (blockMat (m := m) A).det = A.det := by
  unfold blockMat
  rw [Matrix.coe_reindexAlgEquiv, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem blockMat_inl_inl (A : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4) :
    blockMat (m := m) A (Fin.castAdd m i) (Fin.castAdd m j) = A i j := by
  simp [blockMat]

theorem blockMat_inr_inr (A : Matrix (Fin 4) (Fin 4) F) (i j : Fin m) :
    blockMat (m := m) A (Fin.natAdd 4 i) (Fin.natAdd 4 j) = (1 : Matrix (Fin m) (Fin m) F) i j := by
  simp [blockMat]

@[expose] def blockSL (A : SpecialLinearGroup (Fin 4) F) : SpecialLinearGroup (Fin (4 + m)) F :=
  ⟨blockMat A, by rw [det_blockMat]; exact A.2⟩

theorem coe_blockSL (A : SpecialLinearGroup (Fin 4) F) :
    ((blockSL (m := m) A : SpecialLinearGroup (Fin (4 + m)) F) :
      Matrix (Fin (4 + m)) (Fin (4 + m)) F) = blockMat A := rfl

@[expose] def blockHom : SpecialLinearGroup (Fin 4) F →* SpecialLinearGroup (Fin (4 + m)) F where
  toFun := blockSL
  map_one' := by
    apply Subtype.ext
    rw [coe_blockSL, Matrix.SpecialLinearGroup.coe_one]
    exact blockMat_one
  map_mul' A B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL, coe_blockSL,
      Matrix.SpecialLinearGroup.coe_mul]
    exact blockMat_mul _ _

theorem coe_blockHom (A : SpecialLinearGroup (Fin 4) F) :
    ((blockHom (m := m) A : SpecialLinearGroup (Fin (4 + m)) F) :
      Matrix (Fin (4 + m)) (Fin (4 + m)) F) = blockMat A := rfl

theorem blockHom_injective : Function.Injective (blockHom (F := F) (m := m)) := by
  intro A B h
  have h' := congrArg (fun M : SpecialLinearGroup (Fin (4 + m)) F =>
    (M : Matrix (Fin (4 + m)) (Fin (4 + m)) F)) h
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h' (Fin.castAdd m i)) (Fin.castAdd m j)
  simpa [coe_blockHom, blockMat_inl_inl] using this

@[expose] def signMat : Matrix (Fin (4 + m)) (Fin (4 + m)) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv (Matrix.fromBlocks (-1) 0 0 1)

theorem signMat_mul_self : (signMat (F := F) (m := m)) * signMat = 1 := by
  unfold signMat
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one, map_one]

theorem det_signMat : (signMat (F := F) (m := m)).det = 1 := by
  unfold signMat
  rw [Matrix.coe_reindexAlgEquiv, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one, Matrix.det_neg]
  norm_num

@[expose] def signSL : SpecialLinearGroup (Fin (4 + m)) F := ⟨signMat, det_signMat⟩

theorem coe_signSL : ((signSL (F := F) (m := m) : SpecialLinearGroup (Fin (4 + m)) F) :
    Matrix (Fin (4 + m)) (Fin (4 + m)) F) = signMat := rfl

theorem signSL_sq : (signSL (F := F) (m := m)) ^ 2 = 1 := by
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_signSL, signMat_mul_self,
    Matrix.SpecialLinearGroup.coe_one]

theorem blockHom_comm_signSL (A : SpecialLinearGroup (Fin 4) F) :
    blockHom (m := m) A * signSL = signSL * blockHom A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockHom,
    coe_signSL]
  unfold blockMat signMat
  rw [← map_mul, ← map_mul, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem signSL_not_mem_center (hm : 1 ≤ m) (h : (-1 : F) ≠ 1) :
    (signSL (F := F) (m := m)) ∉ Subgroup.center (SpecialLinearGroup (Fin (4 + m)) F) := by
  intro hc
  have hs := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc (Fin.castAdd m (0 : Fin 4))
  have e2 := congrArg (fun M : Matrix (Fin (4 + m)) (Fin (4 + m)) F =>
    M (Fin.natAdd 4 (⟨0, hm⟩ : Fin m)) (Fin.natAdd 4 (⟨0, hm⟩ : Fin m))) hs
  simp [coe_signSL, signMat, Matrix.scalar_apply, Matrix.coe_reindexAlgEquiv] at e2
  exact h e2

end Block

end CFSG.RankThree.PartOne.SLB4B
