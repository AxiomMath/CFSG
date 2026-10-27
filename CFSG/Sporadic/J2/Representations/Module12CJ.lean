module

public import CFSG.Sporadic.J2.Representations.Module12Q

public section

namespace CFSG.Sporadic.J2.Module12

open Module CFSG.RepresentationTheory.GF2

theorem CJ_le_ker (X : Matrix (Fin 12) (Fin 12) (ZMod 2)) (hX : X ∈ CJ) : Phi X = 0 := by
  funext i
  have hX' : X * Jm = Jm * X := hX
  show (X * Jm + Jm * X) (eqIdx i).1 (eqIdx i).2 = 0
  rw [hX', Matrix.add_apply]
  exact CharTwo.add_self_eq_zero _

theorem span_le_Aalg :
    Submodule.span (ZMod 2) (Set.range wmat) ≤ Aalg.toSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact wmat_mem_Aalg j

theorem qIdx_coord (j : Fin 72) :
    12 * (qIdx j).1.val + (qIdx j).2.val = 72 + j.val := by
  revert j
  decide +kernel

theorem qIdx_injective : Function.Injective qIdx := by
  intro a b h
  have ha := qIdx_coord a
  have hb := qIdx_coord b
  rw [h] at ha
  exact Fin.ext (by omega)

theorem qIdx_surj_ge {r c : Fin 12} (h : 72 ≤ 12 * r.val + c.val) :
    ∃ j : Fin 72, qIdx j = (r, c) := by
  have hr : r.val < 12 := r.isLt
  have hc : c.val < 12 := c.isLt
  let j : Fin 72 := ⟨12 * r.val + c.val - 72, by omega⟩
  refine ⟨j, ?_⟩
  have hcoord := qIdx_coord j
  have hb : (qIdx j).2.val < 12 := (qIdx j).2.isLt
  have hj : j.val = 12 * r.val + c.val - 72 := rfl
  have h1 : (qIdx j).1.val = r.val := by omega
  have h2 : (qIdx j).2.val = c.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem sum_singleMat_of_zero_on_Q (Z : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hZ : ∀ k : Fin 72, Z (Qrow k) (Qcol k) = 0) :
    Z = ∑ j : Fin 72, Z (qIdx j).1 (qIdx j).2 • singleMat (qIdx j) := by
  ext r c
  rw [Matrix.sum_apply]
  by_cases hin : ∃ j : Fin 72, qIdx j = (r, c)
  · obtain ⟨j, hj⟩ := hin
    rw [Finset.sum_eq_single j]
    · rw [Matrix.smul_apply, smul_eq_mul, hj, singleMat]
      simp
    · intro b _ hbj
      have hne : qIdx b ≠ (r, c) := by
        intro hbc
        exact hbj (qIdx_injective (hbc.trans hj.symm))
      have hcond : ¬ (r = (qIdx b).1 ∧ c = (qIdx b).2) := by
        rintro ⟨h1, h2⟩
        exact hne (Prod.ext h1.symm h2.symm)
      rw [Matrix.smul_apply, smul_eq_mul, singleMat]
      simp [hcond]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · have hin' : ∀ j : Fin 72, qIdx j ≠ (r, c) := by
      intro j hj
      exact hin ⟨j, hj⟩
    have hr : r.val < 12 := r.isLt
    have hc : c.val < 12 := c.isLt
    have hlt : 12 * r.val + c.val < 72 := by
      by_contra hge
      obtain ⟨j, hj⟩ := qIdx_surj_ge (by omega : 72 ≤ 12 * r.val + c.val)
      exact hin' j hj
    have hQR : Qrow ⟨12 * r.val + c.val, hlt⟩ = r := by
      ext
      rw [Qrow_val, Q_val]
      change (12 * r.val + c.val) / 12 = r.val
      omega
    have hQC : Qcol ⟨12 * r.val + c.val, hlt⟩ = c := by
      ext
      rw [Qcol_val, Q_val]
      change (12 * r.val + c.val) % 12 = c.val
      omega
    have hZrc : Z r c = 0 := by
      have hk := hZ ⟨12 * r.val + c.val, hlt⟩
      rwa [hQR, hQC] at hk
    rw [hZrc]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hne : qIdx j ≠ (r, c) := hin' j
    have hcond : ¬ (r = (qIdx j).1 ∧ c = (qIdx j).2) := by
      rintro ⟨h1, h2⟩
      exact hne (Prod.ext h1.symm h2.symm)
    rw [Matrix.smul_apply, smul_eq_mul, singleMat]
    simp [hcond]

def T (c : Fin 72 → ZMod 2) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ∑ j : Fin 72, c j • singleMat (qIdx j)

theorem Phi_T (c : Fin 72 → ZMod 2) (i : Fin 72) :
    Phi (T c) i = ∑ j : Fin 72, c j * Fmat i j := by
  rw [T, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem eq_zero_of_Phi_zero_of_zero_on_Q (Z : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hZQ : ∀ k : Fin 72, Z (Qrow k) (Qcol k) = 0) (hPhi : Phi Z = 0) : Z = 0 := by
  let z : Fin 72 → ZMod 2 := fun j => Z (qIdx j).1 (qIdx j).2
  have hdecomp : Z = T z := by
    simpa [T, z] using sum_singleMat_of_zero_on_Q Z hZQ
  have hPhiT : Phi (T z) = 0 := by
    rw [← hdecomp]
    exact hPhi
  have hz : z = 0 := by
    have hz0 : Matrix.mulVec Fmat z = 0 := by
      funext i
      have h1 := congrFun hPhiT i
      rw [Phi_T z i] at h1
      simpa [Matrix.mulVec_apply_eq_sum, mul_comm] using h1
    have hinj := mulVec_injective_of_mul_eq_one (A := Fmat) (B := FinvMat) FinvMat_mul
    apply hinj
    rw [hz0, Matrix.mulVec_zero]
  rw [hdecomp, hz]
  simp [T]

theorem wmat_apply_Qrow (j k : Fin 72) :
    wmat j (Qrow k) (Qcol k) = WQmat j k := by
  simp [wmat, matOfMask, WQmat, Qrow_col]

theorem CJ_le_span (X : Matrix (Fin 12) (Fin 12) (ZMod 2)) (hX : X ∈ CJ) :
    X ∈ Submodule.span (ZMod 2) (Set.range wmat) := by
  let v : Fin 72 → ZMod 2 := fun k => X (Qrow k) (Qcol k)
  let c : Fin 72 → ZMod 2 := Matrix.mulVec WQinv.transpose v
  let Y : Matrix (Fin 12) (Fin 12) (ZMod 2) := ∑ j : Fin 72, c j • wmat j
  have hWQt : WQmat.transpose * WQinv.transpose = 1 := by
    rw [← Matrix.transpose_mul, WQinv_mul, Matrix.transpose_one]
  have hYQ : ∀ k : Fin 72, Y (Qrow k) (Qcol k) = v k := by
    intro k
    calc
      Y (Qrow k) (Qcol k) = ∑ j : Fin 72, c j * wmat j (Qrow k) (Qcol k) := by
        simp only [Y, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      _ = ∑ j : Fin 72, c j * WQmat j k := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [wmat_apply_Qrow j k]
      _ = Matrix.mulVec WQmat.transpose c k := by
        rw [Matrix.mulVec_apply_eq_sum]
        simp only [Matrix.transpose_apply]
        exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = v k := by
        dsimp only [c]
        rw [Matrix.mulVec_mulVec (v := v) (M := WQmat.transpose) (N := WQinv.transpose)]
        rw [hWQt, Matrix.one_mulVec]
  have hYspan : Y ∈ Submodule.span (ZMod 2) (Set.range wmat) := by
    dsimp only [Y]
    refine Submodule.sum_mem (p := Submodule.span (ZMod 2) (Set.range wmat))
      (t := Finset.univ) ?_
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hYCJ : Y ∈ CJ := Aalg_le_CJ (span_le_Aalg hYspan)
  have hXYCJ : X - Y ∈ CJ := CJ.sub_mem hX hYCJ
  have hQ : ∀ k : Fin 72, (X - Y) (Qrow k) (Qcol k) = 0 := by
    intro k
    have h := hYQ k
    dsimp only [v] at h
    rw [Matrix.sub_apply, h, sub_self]
  have hPhi : Phi (X - Y) = 0 := CJ_le_ker (X - Y) hXYCJ
  have hzero : X - Y = 0 := eq_zero_of_Phi_zero_of_zero_on_Q (X - Y) hQ hPhi
  rw [sub_eq_zero.mp hzero]
  exact hYspan

theorem Aalg_eq_CJ :
    (Aalg : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) =
      (CJ : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) := by
  ext X
  exact ⟨fun hX => Aalg_le_CJ hX, fun hX => span_le_Aalg (CJ_le_span X hX)⟩

theorem Jm_mem_Aalg : Jm ∈ Aalg := by
  have h : Jm ∈ CJ := by
    show Jm * Jm = Jm * Jm
    rfl
  have hmem : Jm ∈ (Aalg : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) ↔
      Jm ∈ (CJ : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) := by
    rw [Aalg_eq_CJ]
  exact hmem.mpr h

end CFSG.Sporadic.J2.Module12
