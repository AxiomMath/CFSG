module

public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.RankThree.PartTwo.Sec4.LThreePiUnitary
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.CTU6

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan (blockMat blockSel blockSel_apply blockSel_transpose_mul_self
  blockMat_mul blockMat_one det_blockMat conjTr_blockMat blockMat_apply blockMat_injective blockGL
  coe_blockGL)
open CFSG.RankThree.PartTwo.Sec4 (conjTr_conjTr_of_invol det_conjTr)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem antidiag_transpose (n : ℕ) : (antidiag n : Matrix (Fin n) (Fin n) F)ᵀ = antidiag n := by
  ext i j
  simp only [transpose_apply, antidiag, of_apply]
  by_cases h : j = Fin.rev i
  · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), ite_eq_left_iff.mpr
      (fun h' => absurd (by rw [h, Fin.rev_rev]) h')]
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), ite_eq_right_iff.mpr
      (fun h' => absurd (by rw [h', Fin.rev_rev]) h)]

theorem conjTr_antidiag (σ : F ≃+* F) (n : ℕ) :
    conjTr σ (antidiag n : Matrix (Fin n) (Fin n) F) = antidiag n := by
  have h : (antidiag n : Matrix (Fin n) (Fin n) F).map σ = antidiag n := by
    ext i j
    simp only [map_apply, antidiag, of_apply]
    split_ifs <;> simp
  rw [conjTr, h, antidiag_transpose]

theorem antidiag_mul_blockSel :
    (antidiag 6 : Matrix (Fin 6) (Fin 6) F) * blockSel F 6 4 1 =
      blockSel F 6 4 1 * (antidiag 4 : Matrix (Fin 4) (Fin 4) F) := by
  ext a j
  rw [mul_apply, mul_apply]
  fin_cases a <;> fin_cases j <;>
    simp [antidiag, blockSel_apply, Fin.sum_univ_succ, Fin.rev]

theorem blockMat_isometry (σ : F ≃+* F) {A : Matrix (Fin 4) (Fin 4) F}
    (hA : conjTr σ A * antidiag 4 * A = antidiag 4) :
    conjTr σ (blockMat 6 1 A) * antidiag 6 * blockMat 6 1 A = antidiag 6 := by
  rw [conjTr_blockMat]
  have hL : (blockSel F 6 4 1)ᵀ * blockSel F 6 4 1 = 1 := blockSel_transpose_mul_self (by norm_num)
  have h1 := antidiag_mul_blockSel (F := F)
  have h2 : (blockSel F 6 4 1)ᵀ * (antidiag 6 : Matrix (Fin 6) (Fin 6) F) =
      (antidiag 4 : Matrix (Fin 4) (Fin 4) F) * (blockSel F 6 4 1)ᵀ := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_mul, antidiag_transpose, antidiag_transpose] at this
  unfold blockMat
  set L := blockSel F 6 4 1
  set J := (antidiag 6 : Matrix (Fin 6) (Fin 6) F)
  set J' := (antidiag 4 : Matrix (Fin 4) (Fin 4) F)
  set X := conjTr σ A - 1 with hX
  set Y := A - 1 with hY
  have key : J' * Y + X * J' + X * J' * Y = 0 := by
    have e : conjTr σ A = X + 1 := by rw [hX, sub_add_cancel]
    have e' : A = Y + 1 := by rw [hY, sub_add_cancel]
    rw [e, e'] at hA
    have : (X + 1) * J' * (Y + 1) - J' = J' * Y + X * J' + X * J' * Y := by noncomm_ring
    rw [← this, hA, sub_self]
  have e1 : J * (L * Y * Lᵀ) = L * (J' * Y) * Lᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc L J' Y]
  have e2 : L * X * Lᵀ * J = L * (X * J') * Lᵀ := by
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, Matrix.mul_assoc L X J']
  have e3 : L * X * Lᵀ * J * (L * Y * Lᵀ) = L * (X * J' * Y) * Lᵀ := by
    rw [e2]
    calc L * (X * J') * Lᵀ * (L * Y * Lᵀ) = L * (X * J') * (Lᵀ * L) * Y * Lᵀ := by
          simp only [Matrix.mul_assoc]
      _ = L * (X * J' * Y) * Lᵀ := by rw [hL, Matrix.mul_one, Matrix.mul_assoc L (X * J') Y]
  calc (1 + L * X * Lᵀ) * J * (1 + L * Y * Lᵀ)
      = J + J * (L * Y * Lᵀ) + L * X * Lᵀ * J + L * X * Lᵀ * J * (L * Y * Lᵀ) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
        abel
    _ = J + L * (J' * Y + X * J' + X * J' * Y) * Lᵀ := by
        rw [e3, e1, e2, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
        abel
    _ = J := by rw [key, Matrix.mul_zero, Matrix.zero_mul, add_zero]

@[expose] noncomputable def embSU4 (σ : F ≃+* F) : SU σ 4 →* SU σ 6 :=
  ((blockGL 6 1 (by norm_num)).comp (SU σ 4).subtype).codRestrict (SU σ 6) fun g =>
    ⟨by rw [MonoidHom.comp_apply, coe_blockGL, det_blockMat (by norm_num)]; exact g.2.1,
      by rw [MonoidHom.comp_apply, coe_blockGL]; exact blockMat_isometry σ g.2.2⟩

theorem coe_embSU4 (σ : F ≃+* F) (g : SU σ 4) :
    (((embSU4 σ g : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      blockMat 6 1 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
  rfl

theorem embSU4_injective (σ : F ≃+* F) : Function.Injective (embSU4 σ) := by
  intro g g' h
  have h' := congrArg (fun x : SU σ 6 => ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) h
  simp only [coe_embSU4] at h'
  exact Subtype.ext (Units.ext (blockMat_injective (by norm_num) h'))

@[expose] def pairMat (M N : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks M 0 0 N)

theorem pairMat_mul (M N M' N' : Matrix (Fin 3) (Fin 3) F) :
    pairMat M N * pairMat M' N' = pairMat (M * M') (N * N') := by
  simp only [pairMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem pairMat_one : pairMat (1 : Matrix (Fin 3) (Fin 3) F) 1 = 1 := by
  simp [pairMat, fromBlocks_one]

theorem det_pairMat (M N : Matrix (Fin 3) (Fin 3) F) : (pairMat M N).det = M.det * N.det := by
  rw [pairMat, det_reindex_self, det_fromBlocks_zero₂₁]

theorem conjTr_pairMat (σ : F ≃+* F) (M N : Matrix (Fin 3) (Fin 3) F) :
    conjTr σ (pairMat M N) = pairMat (conjTr σ M) (conjTr σ N) := by
  rw [conjTr, conjTr, conjTr, pairMat, pairMat, reindex_apply, reindex_apply, ← submatrix_map,
    transpose_submatrix, fromBlocks_map, fromBlocks_transpose, Matrix.map_zero _ (map_zero σ),
    transpose_zero]

theorem pairMat_apply (M N : Matrix (Fin 3) (Fin 3) F) (a b : Fin 6) :
    pairMat M N a b =
      if h : a.val < 3 ∧ b.val < 3 then M ⟨a.val, h.1⟩ ⟨b.val, h.2⟩
      else if h' : 3 ≤ a.val ∧ 3 ≤ b.val then
        N ⟨a.val - 3, by omega⟩ ⟨b.val - 3, by omega⟩
      else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

theorem antidiag_six_eq :
    (antidiag 6 : Matrix (Fin 6) (Fin 6) F) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 0 (antidiag 3) (antidiag 3) 0) := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem pairMat_mul_antidiag_mul (M N M' N' : Matrix (Fin 3) (Fin 3) F) :
    pairMat M N * (antidiag 6 : Matrix (Fin 6) (Fin 6) F) * pairMat M' N' =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks 0 (M * antidiag 3 * N') (N * antidiag 3 * M') 0) := by
  rw [antidiag_six_eq]
  simp only [pairMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem coe_inv_eq_of_mul_eq_one {n : ℕ} {M : SL(n, F)} {M' : Matrix (Fin n) (Fin n) F}
    (h : M' * M = 1) : ((M⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = M' := by
  have h1 : ((M⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) * M = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (M : Matrix (Fin n) (Fin n) F) * M' = 1 := _root_.mul_eq_one_comm.mp h
  calc ((M⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)
      = ((M⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) * (M * M') := by rw [h2, Matrix.mul_one]
    _ = M' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

variable (σ : F ≃+* F)

@[expose] def lowBlk (M : SL(3, F)) : Matrix (Fin 3) (Fin 3) F :=
  (antidiag 3 : Matrix (Fin 3) (Fin 3) F) * conjTr σ ((M⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
    antidiag 3

@[expose] def embSL3Mat (M : SL(3, F)) : Matrix (Fin 6) (Fin 6) F :=
  pairMat (M : Matrix (Fin 3) (Fin 3) F) (lowBlk σ M)

theorem lowBlk_mul (M M' : SL(3, F)) : lowBlk σ (M * M') = lowBlk σ M * lowBlk σ M' := by
  have hJ := antidiag_mul_self (F := F) 3
  simp only [lowBlk, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, conjTr_mul]
  set J := (antidiag 3 : Matrix (Fin 3) (Fin 3) F)
  set C := conjTr σ ((M⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
  set C' := conjTr σ ((M'⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
  calc J * (C * C') * J = J * C * (J * J) * C' * J := by
        rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = J * C * J * (J * C' * J) := by simp only [Matrix.mul_assoc]

theorem lowBlk_one : lowBlk σ (1 : SL(3, F)) = 1 := by
  rw [lowBlk, inv_one, Matrix.SpecialLinearGroup.coe_one, conjTr_one, Matrix.mul_one,
    antidiag_mul_self]

theorem det_lowBlk (M : SL(3, F)) : (lowBlk σ M).det = 1 := by
  have hJ := congrArg Matrix.det (antidiag_mul_self (F := F) 3)
  rw [det_mul, det_one] at hJ
  rw [lowBlk, det_mul, det_mul, det_conjTr, (M⁻¹).2, map_one, mul_one, hJ]

theorem det_embSL3Mat (M : SL(3, F)) : (embSL3Mat σ M).det = 1 := by
  rw [embSL3Mat, det_pairMat, M.2, det_lowBlk, one_mul]

theorem embSL3Mat_mul (M M' : SL(3, F)) :
    embSL3Mat σ (M * M') = embSL3Mat σ M * embSL3Mat σ M' := by
  rw [embSL3Mat, embSL3Mat, embSL3Mat, pairMat_mul, lowBlk_mul, Matrix.SpecialLinearGroup.coe_mul]

theorem embSL3Mat_one : embSL3Mat σ (1 : SL(3, F)) = 1 := by
  rw [embSL3Mat, lowBlk_one, Matrix.SpecialLinearGroup.coe_one, pairMat_one]

theorem embSL3Mat_isometry (hσ : ∀ c, σ (σ c) = c) (M : SL(3, F)) :
    conjTr σ (embSL3Mat σ M) * antidiag 6 * embSL3Mat σ M = antidiag 6 := by
  have hJ := antidiag_mul_self (F := F) 3
  have hJt := conjTr_antidiag (F := F) σ 3
  set J := (antidiag 3 : Matrix (Fin 3) (Fin 3) F)
  set Mi := ((M⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
  have hMi : Mi * (M : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e1 : conjTr σ (M : Matrix (Fin 3) (Fin 3) F) * J * lowBlk σ M = J := by
    calc conjTr σ (M : Matrix (Fin 3) (Fin 3) F) * J * lowBlk σ M
        = conjTr σ (M : Matrix (Fin 3) (Fin 3) F) * (J * J) * conjTr σ Mi * J := by
          simp only [lowBlk, Matrix.mul_assoc]; rfl
      _ = conjTr σ (Mi * (M : Matrix (Fin 3) (Fin 3) F)) * J := by
          rw [hJ, Matrix.mul_one, conjTr_mul]
      _ = J := by rw [hMi, conjTr_one, Matrix.one_mul]
  have e2 : conjTr σ (lowBlk σ M) * J * (M : Matrix (Fin 3) (Fin 3) F) = J := by
    have hc : conjTr σ (lowBlk σ M) = J * Mi * J := by
      simp only [lowBlk, conjTr_mul, conjTr_conjTr_of_invol hσ]
      rw [hJt]
      simp only [Matrix.mul_assoc]
      rfl
    rw [hc]
    calc J * Mi * J * J * (M : Matrix (Fin 3) (Fin 3) F)
        = J * Mi * (J * J) * (M : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hJ, Matrix.mul_one, Matrix.mul_assoc, hMi, Matrix.mul_one]
  rw [embSL3Mat, conjTr_pairMat, pairMat_mul_antidiag_mul, e1, e2, antidiag_six_eq]

@[expose] noncomputable def embSL3 (hσ : ∀ c, σ (σ c) = c) : SL(3, F) →* SU σ 6 where
  toFun M := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (embSL3Mat σ M)
      (by rw [det_embSL3Mat]; exact one_ne_zero), det_embSL3Mat σ M, embSL3Mat_isometry σ hσ M⟩
  map_one' := Subtype.ext (Units.ext (embSL3Mat_one σ))
  map_mul' M M' := Subtype.ext (Units.ext (embSL3Mat_mul σ M M'))

theorem coe_embSL3 (hσ : ∀ c, σ (σ c) = c) (M : SL(3, F)) :
    (((embSL3 σ hσ M : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = embSL3Mat σ M :=
  rfl

theorem embSL3_injective (hσ : ∀ c, σ (σ c) = c) : Function.Injective (embSL3 σ hσ) := by
  intro M M' h
  have h' := congrArg (fun x : SU σ 6 => ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) h
  simp only [coe_embSL3] at h'
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have := congrFun (congrFun h' ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  simpa [embSL3Mat, pairMat_apply] using this

end CFSG.RankThree.PartTwo.CTU6
