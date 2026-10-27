module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47L3Cls
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47L3Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped MatrixGroups Matrix

open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open CFSG.RankThree.SubgroupLists

private theorem s16c1_G47_L3_blkMat_neg_one {F : Type} [Field F] :
    blkMat (-1 : Matrix (Fin 2) (Fin 2) F) 1 = Matrix.diagonal ![-1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

private theorem s16c1_G47_L3_blkMat_conj_fix {F : Type} [Field F]
    {Pm Pi Bm B'' N : Matrix (Fin 3) (Fin 3) F}
    (hPiPm : Pi * Pm = 1) (hPmTPiT : Pm.transpose * Pi.transpose = 1)
    (hB'' : B'' = Pi * Bm * Pi.transpose)
    (h : Pm * (N * B'' * N.transpose) * Pm.transpose = Bm) :
    N * B'' * N.transpose = B'' := by
  have h1 : Pi * (Pm * (N * B'' * N.transpose) * Pm.transpose) * Pi.transpose
      = N * B'' * N.transpose := by
    rw [← mul_assoc Pi (Pm * (N * B'' * N.transpose)) Pm.transpose,
      ← mul_assoc Pi Pm (N * B'' * N.transpose),
      hPiPm, one_mul,
      mul_assoc (N * B'' * N.transpose) Pm.transpose Pi.transpose,
      hPmTPiT, mul_one]
  rw [h] at h1
  exact (hB''.trans h1).symm

theorem s16c1_G47_L3_inner {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {X : Subgroup SL(3, F)} (hX : IsSL2Prime ↥X 5) {g : SL(3, F)} (hg2 : g * g = 1)
    (hg1 : g ≠ 1) (hgX : ∀ x ∈ X, g * x = x * g) : g ∈ X := by
  have h2 : (2 : F) ≠ 0 :=
    CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F (by rw [hF]; norm_num)
  obtain ⟨P, hPX, hPA⟩ := s16c1_G47_L3_std_mem hF hX
  obtain ⟨t0, ht0X, ht0eq⟩ := hPA (-1 : SL(2, F))
  have ht0mat : ((t0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F) * negDiag3 F *
        ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [ht0eq, show ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 by simp,
      s16c1_G47_L3_blkMat_neg_one (F := F), ← coe_negDiag3]
  have ht0GL : (t0 : GL (Fin 3) F) = P * negDiag3 F * P⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact ht0mat
  have hgt0 : g * t0 = t0 * g := hgX t0 ht0X
  have hgcomm : (g : GL (Fin 3) F) * (t0 : GL (Fin 3) F) =
      (t0 : GL (Fin 3) F) * (g : GL (Fin 3) F) := by
    have h := congrArg (fun z : SL(3, F) => (z : GL (Fin 3) F)) hgt0
    simpa [map_mul] using h
  set Y : GL (Fin 3) F := P⁻¹ * (g : GL (Fin 3) F) * P with hY
  have hYcomm : Y * negDiag3 F = negDiag3 F * Y := by
    have hconj : P⁻¹ * (t0 : GL (Fin 3) F) * P = negDiag3 F := by
      rw [ht0GL]; group
    calc Y * negDiag3 F = Y * (P⁻¹ * (t0 : GL (Fin 3) F) * P) := by rw [hconj]
      _ = (P⁻¹ * (g : GL (Fin 3) F) * P) * (P⁻¹ * (t0 : GL (Fin 3) F) * P) := by
            rw [hY]
      _ = P⁻¹ * ((g : GL (Fin 3) F) * (t0 : GL (Fin 3) F)) * P := by group
      _ = P⁻¹ * ((t0 : GL (Fin 3) F) * (g : GL (Fin 3) F)) * P := by rw [hgcomm]
      _ = (P⁻¹ * (t0 : GL (Fin 3) F) * P) * (P⁻¹ * (g : GL (Fin 3) F) * P) := by group
      _ = negDiag3 F * Y := by rw [hconj, hY]
  have hYdet : (Y : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [hY, Units.val_mul, Units.val_mul, Matrix.det_units_conj']
    exact Matrix.SpecialLinearGroup.det_coe g
  obtain ⟨A0, hA0⟩ := exists_blk_of_commute h2 hYcomm hYdet
  have hA0comm : ∀ A : SL(2, F), (A0 : Matrix (Fin 2) (Fin 2) F) *
      (A : Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F) *
        (A0 : Matrix (Fin 2) (Fin 2) F) := by
    intro A
    obtain ⟨x, hxX, hxM⟩ := hPA A
    have hxGL : (x : GL (Fin 3) F) = P * blk A * P⁻¹ := by
      apply Units.ext
      have hblkA : ((blk A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 := by
        rw [coe_blk, show ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F) from rfl,
          Matrix.SpecialLinearGroup.det_coe, inv_one]
      rw [Units.val_mul, Units.val_mul, hblkA]
      exact hxM
    have hgx : (g : GL (Fin 3) F) * (x : GL (Fin 3) F) =
        (x : GL (Fin 3) F) * (g : GL (Fin 3) F) := by
      have h := congrArg (fun z : SL(3, F) => (z : GL (Fin 3) F)) (hgX x hxX)
      simpa [map_mul] using h
    have hxconj : P⁻¹ * (x : GL (Fin 3) F) * P = blk A := by
      rw [hxGL]; group
    have hYx : Y * blk A = blk A * Y := by
      calc Y * blk A = (P⁻¹ * (g : GL (Fin 3) F) * P) *
            (P⁻¹ * (x : GL (Fin 3) F) * P) := by rw [hY, hxconj]
        _ = P⁻¹ * ((g : GL (Fin 3) F) * (x : GL (Fin 3) F)) * P := by group
        _ = P⁻¹ * ((x : GL (Fin 3) F) * (g : GL (Fin 3) F)) * P := by rw [hgx]
        _ = (P⁻¹ * (x : GL (Fin 3) F) * P) * (P⁻¹ * (g : GL (Fin 3) F) * P) := by group
        _ = blk A * Y := by rw [hxconj, hY]
    have hblkcomm : blk A0 * blk A = blk A * blk A0 := by rw [hA0]; exact hYx
    have hul := congrArg (fun z : GL (Fin 3) F => ulBlock (z : Matrix (Fin 3) (Fin 3) F))
      hblkcomm
    simp only [Units.val_mul, coe_blk, Matrix.SpecialLinearGroup.det_coe, inv_one,
      blkMat_mul, ulBlock_blkMat] at hul
    exact hul
  obtain ⟨c, hc⟩ := s16c1_G47_sl2_cent_scalar (A0 : Matrix (Fin 2) (Fin 2) F) hA0comm
  have hY2 : Y * Y = 1 := by
    have hgg : (g : GL (Fin 3) F) * (g : GL (Fin 3) F) = 1 := by
      have h := congrArg (fun z : SL(3, F) => (z : GL (Fin 3) F)) hg2
      simpa [map_mul] using h
    calc Y * Y = (P⁻¹ * (g : GL (Fin 3) F) * P) * (P⁻¹ * (g : GL (Fin 3) F) * P) := by
          rw [hY]
      _ = P⁻¹ * ((g : GL (Fin 3) F) * (g : GL (Fin 3) F)) * P := by group
      _ = 1 := by rw [hgg]; group
  have hA0sq : A0 * A0 = 1 := by
    apply blk_injective
    rw [map_mul, hA0, hY2, map_one]
  have hcc : c * c = 1 := by
    have h := congrArg (fun z : GL (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F) 0 0) hA0sq
    simp only [Units.val_mul, Units.val_one, hc] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, smul_eq_mul] using h
  rcases mul_self_eq_one_iff.mp hcc with hc1 | hcneg
  · exfalso
    have hA0one : A0 = 1 := by
      apply Units.ext
      rw [hc, hc1, one_smul, Units.val_one]
    have hY1 : Y = 1 := by rw [← hA0, hA0one, map_one]
    have hgGL : (g : GL (Fin 3) F) = 1 := by
      have h : P⁻¹ * (g : GL (Fin 3) F) * P = 1 := by rw [← hY, hY1]
      calc (g : GL (Fin 3) F) = P * (P⁻¹ * (g : GL (Fin 3) F) * P) * P⁻¹ := by group
        _ = P * 1 * P⁻¹ := by rw [h]
        _ = 1 := by group
    exact hg1 (Matrix.SpecialLinearGroup.toGL_injective (by simpa using hgGL))
  · have hA0neg : (A0 : Matrix (Fin 2) (Fin 2) F) = -1 := by
      rw [hc, hcneg, neg_one_smul]
    have hdetA0 : (A0 : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [hA0neg, Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
      ring
    have hblkA0 : blk A0 = negDiag3 F := by
      apply Units.ext
      rw [coe_blk, hdetA0, hA0neg, inv_one, s16c1_G47_L3_blkMat_neg_one (F := F),
        coe_negDiag3]
    have hYneg : Y = negDiag3 F := by rw [← hA0, hblkA0]
    have hgGL : (g : GL (Fin 3) F) = (t0 : GL (Fin 3) F) := by
      have h : P⁻¹ * (g : GL (Fin 3) F) * P = negDiag3 F := by rw [← hY, hYneg]
      calc (g : GL (Fin 3) F) = P * (P⁻¹ * (g : GL (Fin 3) F) * P) * P⁻¹ := by group
        _ = P * negDiag3 F * P⁻¹ := by rw [h]
        _ = (t0 : GL (Fin 3) F) := by rw [ht0GL]
    have hgt0' : g = t0 := Matrix.SpecialLinearGroup.toGL_injective hgGL
    rw [hgt0']
    exact ht0X

theorem s16c1_G47_L3_outer {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {X : Subgroup SL(3, F)} (hX : IsSL2Prime ↥X 5) (σ : MulAut SL(3, F)) (B : GL (Fin 3) F)
    (hσ : ∀ s : SL(3, F), ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hσX : ∀ x ∈ X, σ x = x) : ∃ s : SL(3, F), σ (σ s) ≠ s := by
  classical
  by_contra hcon
  push Not at hcon
  have h2 : (2 : F) ≠ 0 :=
    CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F (by rw [hF]; norm_num)
  obtain ⟨P, hPX, hPA⟩ := s16c1_G47_L3_std_mem hF hX
  set Pm : Matrix (Fin 3) (Fin 3) F := (P : Matrix (Fin 3) (Fin 3) F) with hPm
  set Pi : Matrix (Fin 3) (Fin 3) F :=
    ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hPi
  set Bm : Matrix (Fin 3) (Fin 3) F := (B : Matrix (Fin 3) (Fin 3) F) with hBm
  set Bi : Matrix (Fin 3) (Fin 3) F :=
    ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hBi
  have hBmBi : Bm * Bi = 1 := by
    rw [hBm, hBi]
    exact Units.mul_inv B
  have hBiBm : Bi * Bm = 1 := by
    rw [hBi, hBm]
    exact Units.inv_mul B
  have hPiPm : Pi * Pm = 1 := by
    rw [hPi, hPm]
    exact Units.inv_mul P
  have hPmTPiT : Pm.transpose * Pi.transpose = 1 := by
    rw [← Matrix.transpose_mul Pi Pm, hPiPm, Matrix.transpose_one]
  set W : Matrix (Fin 3) (Fin 3) F := Bm * Bi.transpose with hW
  set W' : Matrix (Fin 3) (Fin 3) F := Bm.transpose * Bi with hW'
  have hBiBmT : Bi.transpose * Bm.transpose = 1 := by
    rw [← Matrix.transpose_mul Bm, hBmBi, Matrix.transpose_one]
  have hW'W : W' * W = 1 := by
    rw [hW', hW]
    calc Bm.transpose * Bi * (Bm * Bi.transpose)
        = Bm.transpose * (Bi * Bm) * Bi.transpose := by noncomm_ring
      _ = Bm.transpose * 1 * Bi.transpose := by rw [hBiBm]
      _ = Bm.transpose * Bi.transpose := by rw [mul_one]
      _ = (Bi * Bm).transpose := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hBiBm, Matrix.transpose_one]
  have hWW' : W * W' = 1 := by
    rw [hW, hW']
    calc Bm * Bi.transpose * (Bm.transpose * Bi)
        = Bm * (Bi.transpose * Bm.transpose) * Bi := by noncomm_ring
      _ = Bm * (Bm * Bi).transpose * Bi := by rw [← Matrix.transpose_mul Bm Bi]
      _ = Bm * 1 * Bi := by rw [hBmBi, Matrix.transpose_one]
      _ = 1 := by rw [mul_one, hBmBi]
  have hσinv : ∀ s : SL(3, F), ((σ (s⁻¹) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Bm * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose * Bi := by
    intro s
    have h := hσ s⁻¹
    rwa [inv_inv] at h
  have hcomp : ∀ s : SL(3, F), ((σ (σ s) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      W * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * W' := by
    intro s
    have h1 : ((σ (σ s) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        Bm * ((((σ s)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose * Bi :=
      hσ (σ s)
    have h2 : (((σ s)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        ((σ (s⁻¹) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
      rw [(map_inv σ s).symm]
    rw [h2, hσinv s] at h1
    have htrans : (Bm * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose *
        Bi).transpose = Bi.transpose * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
          Bm.transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      noncomm_ring
    rw [htrans] at h1
    rw [hW, hW', h1]
    noncomm_ring
  have hMsW : ∀ s : SL(3, F), W * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * W := by
    intro s
    have h1 : ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        W * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * W' := by
      have h := hcomp s
      rwa [hcon s] at h
    calc W * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
        = W * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (W' * W) := by
            rw [hW'W, mul_one]
      _ = (W * ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * W') * W := by
            noncomm_ring
      _ = ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * W := by rw [← h1]
  have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 3) F, Commute t.toMatrix W := by
    intro t
    have hWs := hMsW t.toSpecialLinearGroup
    have hcoe : ((t.toSpecialLinearGroup : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        t.toMatrix := Matrix.TransvectionStruct.toSpecialLinearGroup_coe t
    rw [hcoe] at hWs
    exact hWs.symm
  obtain ⟨c, hcW⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  have hWsmul : W = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hcW, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hBm_smul : Bm = c • Bm.transpose := by
    calc Bm = Bm * (Bi.transpose * Bm.transpose) := by rw [hBiBmT, mul_one]
      _ = (Bm * Bi.transpose) * Bm.transpose := by noncomm_ring
      _ = W * Bm.transpose := by rw [hW]
      _ = (c • (1 : Matrix (Fin 3) (Fin 3) F)) * Bm.transpose := by rw [hWsmul]
      _ = c • Bm.transpose := by rw [Algebra.smul_mul_assoc, one_mul]
  have hBmT_smul : Bm.transpose = c • Bm := by
    have h := congrArg Matrix.transpose hBm_smul
    simpa [Matrix.transpose_smul, Matrix.transpose_transpose] using h
  have hcc : c * c = 1 := by
    have hEq : Bm = (c * c) • Bm := by
      calc Bm = c • Bm.transpose := hBm_smul
        _ = c • (c • Bm) := by rw [hBmT_smul]
        _ = (c * c) • Bm := by rw [smul_smul]
    have hBm0 : Bm ≠ 0 := by
      intro h0
      have h := hBmBi
      rw [h0, zero_mul] at h
      exact zero_ne_one h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hBm0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
    have hentry : Bm i j = (c * c) * Bm i j := by
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hEq
      rw [show ((c * c) • Bm) i j = (c * c) * Bm i j from rfl] at h
      exact h
    have hmul : (c * c - 1) * Bm i j = 0 := by linear_combination -hentry
    have h1 : c * c - 1 = 0 := (mul_eq_zero.mp hmul).resolve_right hj
    linear_combination h1
  have hdetBm : Bm.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hBmBi
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have hBm_symm : Bm.transpose = Bm := by
    rcases mul_self_eq_one_iff.mp hcc with hc1 | hcneg
    · rw [hBmT_smul, hc1, one_smul]
    · exfalso
      have hdet0 : Bm.det = 0 := by
        have h := congrArg Matrix.det hBmT_smul
        rw [hcneg] at h
        rw [neg_one_smul, Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at h
        have hcast : ((-1 : F) ^ 3) = -1 := by ring
        rw [hcast] at h
        have h2' : (2 : F) * Bm.det = 0 := by linear_combination h
        exact (mul_eq_zero.mp h2').resolve_left h2
      exact hdetBm hdet0
  have hxconj : ∀ x ∈ X, ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Bm *
      (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose = Bm := by
    intro x hx
    have hσxinv : σ (x⁻¹) = x⁻¹ := by rw [map_inv, hσX x hx]
    have h1 : ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        Bm * (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose * Bi := by
      have h := hσ x⁻¹
      rw [inv_inv, hσxinv] at h
      exact h
    have hmul : ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rw [h1] at hmul
    calc ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Bm *
          (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose
        = ((((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Bm *
            (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose) * Bi) * Bm := by
            rw [mul_assoc (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Bm *
              (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose) Bi Bm, hBiBm,
              mul_one]
      _ = (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
            (Bm * (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose * Bi)) * Bm := by
            noncomm_ring
      _ = 1 * Bm := by rw [hmul]
      _ = Bm := one_mul Bm
  set B'' : Matrix (Fin 3) (Fin 3) F := Pi * Bm * Pi.transpose with hB''
  have hB''symm : B''.transpose = B'' := by
    rw [hB'', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hBm_symm]
    noncomm_ring
  have hdetPi : Pi.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hPiPm
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have hdetB'' : B''.det ≠ 0 := by
    rw [hB'', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hdetPi hdetBm) hdetPi
  have hfix : ∀ A : SL(2, F), blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 * B'' *
      (blkMat (A : Matrix (Fin 2) (Fin 2) F) 1).transpose = B'' := by
    intro A
    obtain ⟨x, hxX, hxM⟩ := hPA A
    have htrans : (Pm * blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 * Pi).transpose =
        Pi.transpose * (blkMat (A : Matrix (Fin 2) (Fin 2) F) 1).transpose * Pm.transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      noncomm_ring
    have hX : Pm * (blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 * B'' *
        (blkMat (A : Matrix (Fin 2) (Fin 2) F) 1).transpose) * Pm.transpose = Bm := by
      have hxconj' := hxconj x hxX
      rw [← hxconj']
      rw [hxM, htrans, hB'']
      noncomm_ring
    exact s16c1_G47_L3_blkMat_conj_fix hPiPm hPmTPiT hB'' hX
  let U : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let L : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have eU := congrFun (congrFun (hfix U) 0) 1
  simp [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three,
    Matrix.transpose_apply, blkMat, U] at eU
  have h11 : B'' 1 1 = 0 := eU
  have eU02 := congrFun (congrFun (hfix U) 0) 2
  simp [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three,
    Matrix.transpose_apply, blkMat, U] at eU02
  have h12 : B'' 1 2 = 0 := eU02
  have eU00 := congrFun (congrFun (hfix U) 0) 0
  simp [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three,
    Matrix.transpose_apply, blkMat, U] at eU00
  have h01 : B'' 0 1 = 0 := by
    have h01symm : B'' 1 0 = B'' 0 1 := by
      have hs := congrFun (congrFun hB''symm 1) 0
      rw [Matrix.transpose_apply] at hs
      exact hs.symm
    rw [h01symm] at eU00
    have hmul : (2 : F) * B'' 0 1 = 0 := by linear_combination eU00 - h11
    exact (mul_eq_zero.mp hmul).resolve_left h2
  have eL := congrFun (congrFun (hfix L) 0) 1
  simp [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three,
    Matrix.transpose_apply, blkMat, L] at eL
  have h00 : B'' 0 0 = 0 := eL
  have eL2 := congrFun (congrFun (hfix L) 1) 2
  simp [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three,
    Matrix.transpose_apply, blkMat, L] at eL2
  have h02 : B'' 0 2 = 0 := eL2
  exact hdetB'' (Matrix.det_eq_zero_of_row_eq_zero 0 (by
    intro j
    fin_cases j
    · exact h00
    · exact h01
    · exact h02))

theorem s16c1_G47_L3_inv {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {X : Subgroup SL(3, F)} (hX : IsSL2Prime ↥X 5) :
    ∃ t ∈ X, t * t = 1 ∧ t ≠ 1 ∧ ∀ σ : MulAut SL(3, F), (∀ y, σ (σ y) = y) →
      (∀ x ∈ X, σ x = x) → σ = 1 ∨ ∀ y, σ y = t * y * t⁻¹ := by
  obtain ⟨t, ht2, ht1, huniq⟩ := s16c1_G47_sl2five_unique_involution hX
  refine ⟨(t : SL(3, F)), t.2, congrArg Subtype.val ht2, fun h => ht1 (Subtype.ext h), ?_⟩
  intro σ hσ2 hσX
  rcases s16c1_G47_L3_cls hF σ with ⟨B, hB⟩ | ⟨B, hB⟩
  · obtain ⟨g, hg⟩ := s16c1_G47_gl_scale hF B
    have hσg : ∀ s, σ s = g * s * g⁻¹ := fun s => Subtype.ext ((hB s).trans (hg s).symm)
    have hcent : g * g ∈ Subgroup.center SL(3, F) := by
      rw [Subgroup.mem_center_iff]
      intro s
      have h := hσ2 s
      rw [hσg, hσg] at h
      calc s * (g * g) = (g * (g * s * g⁻¹) * g⁻¹) * (g * g) := by rw [h]
        _ = (g * g) * s := by group
    rw [CFSG.RankThree.PartTwo.Sec4.center_specialLinearGroup_eq_bot
      (s16c1_G47_cube_five hF), Subgroup.mem_bot] at hcent
    have hgX : ∀ x ∈ X, g * x = x * g := by
      intro x hx
      have h := hσX x hx
      rw [hσg] at h
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [h]
    by_cases hg1 : g = 1
    · left
      ext s
      rw [hσg, hg1]
      simp
    · right
      have hgmem : g ∈ X := s16c1_G47_L3_inner hF hX hcent hg1 hgX
      have hgt : (⟨g, hgmem⟩ : ↥X) = t :=
        (huniq ⟨g, hgmem⟩ (Subtype.ext hcent)).resolve_left (fun h => hg1 (congrArg Subtype.val h))
      have hgt' : g = (t : SL(3, F)) := congrArg Subtype.val hgt
      intro y
      rw [hσg, hgt']
  · exfalso
    obtain ⟨s, hs⟩ := s16c1_G47_L3_outer hF hX σ B hB hσX
    exact hs (hσ2 s)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
