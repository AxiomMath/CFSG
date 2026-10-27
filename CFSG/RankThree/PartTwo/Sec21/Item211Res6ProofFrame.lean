module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3PlusInn
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Minus
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open Item211Lie2Proof
open scoped MatrixGroups Matrix

section Frame

variable {K : Type} [Field K]

abbrev IsBlk (M : Matrix (Fin 3) (Fin 3) K) : Prop := Item211Lie2Proof.IsBlock M

@[expose] def upper (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem upper_blockMat (A : Matrix (Fin 2) (Fin 2) K) : upper (blockMat A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem upper_mul {M N : Matrix (Fin 3) (Fin 3) K} (hM : IsBlk M) (hN : IsBlk N) :
    upper (M * N) = upper M * upper N := by
  obtain ⟨hM02, hM12, hM20, hM21⟩ := hM
  obtain ⟨hN02, hN12, hN20, hN21⟩ := hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hM02, hM12, hN20, hN21]

theorem det_eq_det_upper {M : Matrix (Fin 3) (Fin 3) K} (hM : IsBlk M) :
    M.det = (upper M).det * M 2 2 := by
  rw [det_of_isBlock hM, Matrix.det_fin_two]
  rfl

theorem mul_blockMat_eq {M : Matrix (Fin 3) (Fin 3) K} (hM : IsBlk M)
    {X Y : Matrix (Fin 2) (Fin 2) K} (h : Y * upper M = upper M * X) :
    M * blockMat X = blockMat Y * M := by
  obtain ⟨hM02, hM12, hM20, hM21⟩ := hM
  have e : ∀ i j, (Y * upper M) i j = (upper M * X) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [upper, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, hM02, hM12, hM20, hM21] <;>
    first | linear_combination e00 | linear_combination -e00 | linear_combination e01 |
      linear_combination -e01 | linear_combination e10 | linear_combination -e10 |
      linear_combination e11 | linear_combination -e11

theorem isUnit_det_upper {g : GL (Fin 3) K} (hg : IsBlk (g : Matrix (Fin 3) (Fin 3) K)) :
    IsUnit (upper (g : Matrix (Fin 3) (Fin 3) K)).det := by
  have h := (Matrix.isUnits_det_units g).ne_zero
  rw [det_eq_det_upper hg] at h
  exact (left_ne_zero_of_mul h).isUnit

@[expose] noncomputable def upperGL {g : GL (Fin 3) K}
    (hg : IsBlk (g : Matrix (Fin 3) (Fin 3) K)) :
    GL (Fin 2) K :=
  Matrix.nonsingInvUnit _ (isUnit_det_upper hg)

theorem coe_upperGL {g : GL (Fin 3) K} (hg : IsBlk (g : Matrix (Fin 3) (Fin 3) K)) :
    ((upperGL hg : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      upper (g : Matrix (Fin 3) (Fin 3) K) :=
  rfl

@[expose] def jTwo : GL (Fin 2) K :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_jTwo : ((jTwo : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem coe_jTwo_inv :
    (((jTwo : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := rfl

theorem map_jTwo (σ : K ≃+* K) :
    Matrix.GeneralLinearGroup.map (σ : K →+* K) (jTwo : GL (Fin 2) K) = jTwo := by
  apply Units.ext
  change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).map σ = !![0, 1; -1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def iota : SL(2, K) →* projectiveSL 3 K := (proj 3 K).comp blockEmb

theorem iota_apply (A : SL(2, K)) : iota A = proj 3 K (blockEmb A) := rfl

theorem fieldAut_iota (σ : K ≃+* K) (A : SL(2, K)) :
    fieldAut 3 K σ (iota A) = iota (Matrix.SpecialLinearGroup.map (σ : K →+* K) A) := by
  rw [iota_apply, iota_apply, fieldAut_proj]
  congr 1
  apply Subtype.ext
  change ((blockEmb A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map σ = blockMat (A.1.map σ)
  rw [coe_blockEmb]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem jTwo_conj (X : Matrix (Fin 2) (Fin 2) K) :
    (jTwo : GL (Fin 2) K).val * X * ((jTwo : GL (Fin 2) K)⁻¹).val =
      !![X 1 1, -X 1 0; -X 0 1, X 0 0] := by
  rw [coe_jTwo, coe_jTwo_inv, Matrix.eta_fin_two X]
  simp

theorem adjugate_transpose_two (X : Matrix (Fin 2) (Fin 2) K) :
    (X.adjugate)ᵀ = !![X 1 1, -X 1 0; -X 0 1, X 0 0] := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem blockMat_transpose (X : Matrix (Fin 2) (Fin 2) K) : (blockMat X)ᵀ = blockMat Xᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dualAut_iota (A : SL(2, K)) :
    dualAut 3 K (iota A) = iota (CatalogueBHigherLinearAction.slConjugation 2 K jTwo A) := by
  rw [iota_apply, iota_apply, dualAut_proj, ← map_inv]
  congr 1
  apply Subtype.ext
  change ((blockEmb A⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ = _
  rw [coe_blockEmb, coe_blockEmb, blockMat_transpose,
    CatalogueBHigherLinearAction.slConjugation_matrix, jTwo_conj,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_transpose_two]

theorem conjAut_iota {g : GL (Fin 3) K} (hg : IsBlk (g : Matrix (Fin 3) (Fin 3) K))
    (A : SL(2, K)) :
    conjAut 3 K g (iota A) =
      iota (CatalogueBHigherLinearAction.slConjugation 2 K (upperGL hg) A) := by
  rw [iota_apply, iota_apply, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_blockEmb, coe_blockEmb,
    CatalogueBHigherLinearAction.slConjugation_matrix]
  set E := upperGL hg with hE
  have hY : ((E : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) *
      ((E⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * upper (g : Matrix (Fin 3) (Fin 3) K) =
      upper (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [← coe_upperGL hg, ← hE, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  rw [mul_blockMat_eq hg hY, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem map_slConjugation (τ : K ≃+* K) (E : GL (Fin 2) K) (B : SL(2, K)) :
    Matrix.SpecialLinearGroup.map (τ : K →+* K)
        (CatalogueBHigherLinearAction.slConjugation 2 K E B) =
      CatalogueBHigherLinearAction.slConjugation 2 K
        (Matrix.GeneralLinearGroup.map (τ : K →+* K) E)
        (Matrix.SpecialLinearGroup.map (τ : K →+* K) B) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, CatalogueBHigherLinearAction.slConjugation_matrix,
    CatalogueBHigherLinearAction.slConjugation_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul, ← map_inv]
  rfl

theorem map_map_sl (τ σ : K ≃+* K) (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map (τ : K →+* K) (Matrix.SpecialLinearGroup.map (σ : K →+* K) A) =
      Matrix.SpecialLinearGroup.map ((τ * σ : K ≃+* K) : K →+* K) A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, Matrix.map_map]
  rfl

theorem map_slConjugation_jTwo (σ : K ≃+* K) (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map (σ : K →+* K)
        (CatalogueBHigherLinearAction.slConjugation 2 K jTwo A) =
      CatalogueBHigherLinearAction.slConjugation 2 K jTwo
        (Matrix.SpecialLinearGroup.map (σ : K →+* K) A) := by
  rw [map_slConjugation, map_jTwo]

theorem fieldAut_proj_sZero (σ : K ≃+* K) :
    fieldAut 3 K σ (proj 3 K sZero) = proj 3 K sZero := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  change ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map σ = _
  rw [coe_sZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem dualAut_proj_sZero : dualAut 3 K (proj 3 K sZero) = proj 3 K sZero := by
  rw [dualAut_proj]
  congr 1
  apply Subtype.ext
  change (((sZero : SL(3, K))⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ = _
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_sZero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.diagonal]

theorem isBlock_of_conjAut_fix (hK2 : (2 : K) ≠ 0) {g : GL (Fin 3) K}
    (h : conjAut 3 K g (proj 3 K sZero) = proj 3 K sZero) :
    IsBlk (g : Matrix (Fin 3) (Fin 3) K) := by
  rw [conjAut_proj] at h
  obtain ⟨c, -, hc⟩ := Item211Lie2Proof.proj_eq_proj_iff.mp h.symm
  rw [coe_slConjugation] at hc
  have htr : Matrix.trace ((g : Matrix (Fin 3) (Fin 3) K) *
      ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) =
        Matrix.trace ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  rw [hc, Matrix.trace_smul, coe_sZero] at htr
  have h1 : Matrix.trace (Matrix.diagonal ![(-1 : K), -1, 1]) = -1 := by
    simp [Matrix.trace_diagonal, Fin.sum_univ_three]
  rw [h1, smul_eq_mul] at htr
  have hc1 : c = 1 := by linear_combination -htr
  rw [hc1, one_smul] at hc
  apply isBlock_of_commute hK2
  have e : (g : Matrix (Fin 3) (Fin 3) K) * ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.mul_assoc _ ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  rw [e, hc]

theorem exists_block_form [Finite K] (hK2 : (2 : K) ≠ 0) {t : MulAut (projectiveSL 3 K)}
    (ht : t (proj 3 K sZero) = proj 3 K sZero) :
    ∃ (g : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      IsBlk (g : Matrix (Fin 3) (Fin 3) K) ∧
      t = conjAut 3 K g * fieldAut 3 K σ * dualAut 3 K ^ ε := by
  obtain ⟨g, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (le_refl 3)).2 t
  refine ⟨g, σ, ε, hε, isBlock_of_conjAut_fix hK2 ?_, rfl⟩
  have hfd : (fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K sZero) = proj 3 K sZero := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rw [pow_zero, mul_one]; exact fieldAut_proj_sZero σ
    · rw [pow_one, MulAut.mul_apply, dualAut_proj_sZero, fieldAut_proj_sZero]
  have e : (conjAut 3 K g * fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K sZero) =
      conjAut 3 K g ((fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K sZero)) := by
    rw [mul_assoc, MulAut.mul_apply]
  rw [e, hfd] at ht
  exact ht

theorem exists_apply_iota [Finite K] (hK2 : (2 : K) ≠ 0) {t : MulAut (projectiveSL 3 K)}
    (ht : t (proj 3 K sZero) = proj 3 K sZero) :
    ∃ E : GL (Fin 2) K, ∀ A : SL(2, K), t (iota A) =
      iota (CatalogueBHigherLinearAction.slConjugation 2 K E
        (Matrix.SpecialLinearGroup.map
          (ProjectivePlane.linearFieldPart K (le_refl 3) t : K →+* K) A)) := by
  obtain ⟨g, σ, ε, hε, hg, rfl⟩ := exists_block_form hK2 ht
  rw [ProjectivePlane.linearFieldPart_eq (le_refl 3) hε]
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · refine ⟨upperGL hg, fun A => ?_⟩
    rw [pow_zero, mul_one, MulAut.mul_apply, fieldAut_iota, conjAut_iota hg]
  · refine ⟨upperGL hg * jTwo, fun A => ?_⟩
    rw [pow_one, MulAut.mul_apply, MulAut.mul_apply, dualAut_iota, fieldAut_iota,
      conjAut_iota hg, map_slConjugation_jTwo, map_mul, MulAut.mul_apply]

theorem apply_iota_pow {t : MulAut (projectiveSL 3 K)} {σ : K ≃+* K} {E : GL (Fin 2) K}
    (ht : ∀ A : SL(2, K), t (iota A) = iota (CatalogueBHigherLinearAction.slConjugation 2 K E
      (Matrix.SpecialLinearGroup.map (σ : K →+* K) A))) (k : ℕ) (A : SL(2, K)) :
    (t ^ k) (iota A) = iota (CatalogueBHigherLinearAction.slConjugation 2 K
      (ProjectivePlane.twistedProd σ E k)
      (Matrix.SpecialLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) A)) := by
  induction k generalizing A with
  | zero =>
    rw [pow_zero, MulAut.one_apply, ProjectivePlane.twistedProd_zero, map_one, MulAut.one_apply,
      pow_zero]
    congr 1
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ht, ih, ProjectivePlane.twistedProd_succ, map_mul,
      MulAut.mul_apply, map_slConjugation, map_map_sl, ← pow_succ]

theorem exists_scalar_of_slConjugation_eq {E : GL (Fin 2) K}
    (h : ∀ A : SL(2, K), CatalogueBHigherLinearAction.slConjugation 2 K E A = A) :
    ∃ c : K, (E : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hcomm : ∀ A : SL(2, K), (E : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * (E : Matrix (Fin 2) (Fin 2) K) := by
    intro A
    have h1 := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K)) (h A)
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix] at h1
    calc (E : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K)
        = (E : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) *
            ((E⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (E : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc _ ((E⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
            ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (A : Matrix (Fin 2) (Fin 2) K) * (E : Matrix (Fin 2) (Fin 2) K) := by rw [h1]
  let u : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hu := congrArg blockMat (hcomm u)
  have hl := congrArg blockMat (hcomm l)
  rw [blockMat_mul, blockMat_mul] at hu hl
  have hbs := isBlockScalar_of_commute_transvections (isBlock_blockMat _) hu hl
  obtain ⟨-, h01, h10, h00⟩ := hbs
  refine ⟨(E : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
  simp only [blockMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h10 h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]

end Frame

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
