module

public import CFSG.Quasithin.H13.U4ParCoord

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {m : ℕ} {K : Type} [Field K]

@[expose] noncomputable def levMat (A : Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix K :=
  single ie1 ie1 1 + single if1 if1 1 + single ie2 ie2 (A 0 0) + single ie2 if2 (A 0 1) +
    single if2 ie2 (A 1 0) + single if2 if2 (A 1 1)

theorem levMat_apply (A : Matrix (Fin 2) (Fin 2) K) (i j : Ix) :
    levMat A i j = (if ie1 = i ∧ ie1 = j then 1 else 0) + (if if1 = i ∧ if1 = j then 1 else 0) +
      (if ie2 = i ∧ ie2 = j then A 0 0 else 0) + (if ie2 = i ∧ if2 = j then A 0 1 else 0) +
      (if if2 = i ∧ ie2 = j then A 1 0 else 0) + (if if2 = i ∧ if2 = j then A 1 1 else 0) := by
  simp only [levMat, Matrix.add_apply, Matrix.single_apply]

theorem levMat_mul (A B : Matrix (Fin 2) (Fin 2) K) : levMat A * levMat B = levMat (A * B) := by
  ext i j
  rw [mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, Matrix.mul_apply, Fin.sum_univ_two, ie1, ie2, if1, if2]

theorem levMat_one : levMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, one_apply, ie1, ie2, if1, if2]

@[expose] def ixSplit : Ix ≃ Fin 2 ⊕ Fin 2 where
  toFun a := if a = ie1 then .inl 0 else if a = if1 then .inl 1 else if a = ie2 then .inr 0
    else .inr 1
  invFun b := match b with
    | .inl i => if i = 0 then ie1 else if1
    | .inr i => if i = 0 then ie2 else if2
  left_inv a := by
    rcases ix_cases a with rfl | rfl | rfl | rfl <;> decide
  right_inv b := by
    rcases b with i | i <;> fin_cases i <;> decide

theorem det_levMat (A : Matrix (Fin 2) (Fin 2) K) : (levMat A).det = A.det := by
  rw [← det_reindex_self ixSplit]
  have : reindex ixSplit ixSplit (levMat A) = fromBlocks 1 0 0 A := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [levMat_apply, ixSplit, ie1, ie2, if1, if2]
  rw [this, det_fromBlocks_zero₂₁, det_one, one_mul]

variable (h : UnitaryFieldData 2 m K)

theorem levMat_gram {A : Matrix (Fin 2) (Fin 2) K} (hA : A.map h.bar = A) (hdet : A.det = 1) :
    ((levMat A).map h.bar)ᵀ * hypGram 2 0 K * levMat A = hypGram 2 0 K := by
  have := h.charP
  have e00 : h.bar (A 0 0) = A 0 0 := congrFun (congrFun hA 0) 0
  have e01 : h.bar (A 0 1) = A 0 1 := congrFun (congrFun hA 0) 1
  have e10 : h.bar (A 1 0) = A 1 0 := congrFun (congrFun hA 1) 0
  have e11 : h.bar (A 1 1) = A 1 1 := congrFun (congrFun hA 1) 1
  rw [det_fin_two] at hdet
  ext i j
  rw [mul_apply, sum_ix]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, hypGram_apply, hypPartner, ie1, ie2, if1, if2, e00, e01, e10, e11] <;>
    grind

@[expose] noncomputable def slMat (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    Matrix (Fin 2) (Fin 2) K :=
  (A : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype

theorem slMat_mul (A B : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    slMat h (A * B) = slMat h A * slMat h B := by
  simp only [slMat, Matrix.SpecialLinearGroup.coe_mul]
  exact Matrix.map_mul

theorem slMat_one : slMat h (1 : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) = 1 := by
  simp only [slMat, Matrix.SpecialLinearGroup.coe_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem slMat_bar (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    (slMat h A).map h.bar = slMat h A := by
  ext i j
  exact (h.mem_fixedField).mp ((A : Matrix (Fin 2) (Fin 2) h.fixedField) i j).2

theorem det_slMat (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) : (slMat h A).det = 1 := by
  rw [slMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, A.2, map_one]

@[expose] noncomputable def levElt (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    hypSU h 2 0 :=
  ⟨⟨levMat (slMat h A), levMat (slMat h A⁻¹),
    by rw [levMat_mul, ← slMat_mul, mul_inv_cancel, slMat_one, levMat_one],
    by rw [levMat_mul, ← slMat_mul, inv_mul_cancel, slMat_one, levMat_one]⟩,
    mem_gramSU.mpr ⟨levMat_gram h (slMat_bar h A) (det_slMat h A),
      by rw [det_levMat, det_slMat]⟩⟩

theorem coe_levElt (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    (((levElt h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = levMat (slMat h A) :=
  rfl

@[expose] noncomputable def levHom : Matrix.SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h 2 0
    where
  toFun := levElt h
  map_one' := hypSU_ext h (by rw [coe_levElt, slMat_one, levMat_one]; rfl)
  map_mul' A B := hypSU_ext h (by
    rw [coe_levElt, coe_mul_hypSU, coe_levElt, coe_levElt, levMat_mul, slMat_mul])

theorem coe_levHom (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    (((levHom h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = levMat (slMat h A) :=
  rfl

theorem levMat_mul_sMat {A : Matrix (Fin 2) (Fin 2) K} (hA : A.map h.bar = A) (hdet : A.det = 1)
    (x y c : K) :
    levMat A * sMat h x y c =
      sMat h (A 0 0 * x + A 0 1 * y) (A 1 0 * x + A 1 1 * y) c * levMat A := by
  have := h.charP
  have e00 : h.bar (A 0 0) = A 0 0 := congrFun (congrFun hA 0) 0
  have e01 : h.bar (A 0 1) = A 0 1 := congrFun (congrFun hA 0) 1
  have e10 : h.bar (A 1 0) = A 1 0 := congrFun (congrFun hA 1) 0
  have e11 : h.bar (A 1 1) = A 1 1 := congrFun (congrFun hA 1) 1
  rw [det_fin_two] at hdet
  ext i j
  rw [mul_apply, sum_ix, mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, sMat_apply, one_apply, ie1, ie2, if1, if2, map_add, map_mul, e00, e01,
      e10, e11] <;>
    grind

end CFSG.Quasithin.H13.U4Par
