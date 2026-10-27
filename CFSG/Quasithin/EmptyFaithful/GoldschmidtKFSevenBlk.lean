module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] def blockMat (a b c d : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a, b, 0; c, d, 0; 0, 0, 1]

@[expose] def symMat (a b c d : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a * a, 2 * a * b, b * b; a * c, a * d + b * c, b * d; c * c, 2 * c * d, d * d]

@[expose] def symGram (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, -2; 0, 1, 0; -2, 0, 0]

theorem det_blockMat (a b c d : K) : (blockMat a b c d).det = a * d - b * c := by
  simp [blockMat, det_fin_three]

theorem det_symMat (a b c d : K) : (symMat a b c d).det = (a * d - b * c) ^ 3 := by
  simp [symMat, det_fin_three]
  ring

theorem blockMat_mul (a b c d a' b' c' d' : K) :
    blockMat a b c d * blockMat a' b' c' d' =
      blockMat (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem symMat_mul (a b c d a' b' c' d' : K) :
    symMat a b c d * symMat a' b' c' d' =
      symMat (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem symMat_gram (a b c d : K) :
    symMat a b c d * symGram K * (symMat a b c d)ᵀ = (a * d - b * c) ^ 2 • symGram K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, symGram, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[expose] def blockHom (K : Type) [Field K] :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun h := ⟨blockMat ((h : Matrix (Fin 2) (Fin 2) K) 0 0) ((h : Matrix (Fin 2) (Fin 2) K) 0 1)
      ((h : Matrix (Fin 2) (Fin 2) K) 1 0) ((h : Matrix (Fin 2) (Fin 2) K) 1 1), by
    rw [det_blockMat, ← det_fin_two]
    exact h.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMat]
  map_mul' h h' := by
    apply Subtype.ext
    change blockMat _ _ _ _ = blockMat _ _ _ _ * blockMat _ _ _ _
    rw [blockMat_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def symHom (K : Type) [Field K] :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun h := ⟨symMat ((h : Matrix (Fin 2) (Fin 2) K) 0 0) ((h : Matrix (Fin 2) (Fin 2) K) 0 1)
      ((h : Matrix (Fin 2) (Fin 2) K) 1 0) ((h : Matrix (Fin 2) (Fin 2) K) 1 1), by
    rw [det_symMat, ← det_fin_two, h.2]
    norm_num⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symMat]
  map_mul' h h' := by
    apply Subtype.ext
    change symMat _ _ _ _ = symMat _ _ _ _ * symMat _ _ _ _
    rw [symMat_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_blockHom (h : SpecialLinearGroup (Fin 2) K) :
    ((blockHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat ((h : Matrix (Fin 2) (Fin 2) K) 0 0) ((h : Matrix (Fin 2) (Fin 2) K) 0 1)
        ((h : Matrix (Fin 2) (Fin 2) K) 1 0) ((h : Matrix (Fin 2) (Fin 2) K) 1 1) :=
  rfl

theorem coe_symHom (h : SpecialLinearGroup (Fin 2) K) :
    ((symHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      symMat ((h : Matrix (Fin 2) (Fin 2) K) 0 0) ((h : Matrix (Fin 2) (Fin 2) K) 0 1)
        ((h : Matrix (Fin 2) (Fin 2) K) 1 0) ((h : Matrix (Fin 2) (Fin 2) K) 1 1) :=
  rfl

theorem symHom_gram (h : SpecialLinearGroup (Fin 2) K) :
    ((symHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * symGram K *
      ((symHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ = symGram K := by
  rw [coe_symHom, symMat_gram, ← det_fin_two, h.2]
  simp

end CFSG.Quasithin.SBd19F
