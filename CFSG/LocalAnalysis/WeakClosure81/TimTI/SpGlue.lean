module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.Timmesfeld.ARS.CaseMSp

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Open CFSG.Timmesfeld.ARS
open CFSG.LieType.Universal.Symplectic
open scoped Matrix

private theorem timti_rank_vecMulVec_eq_one {ι κ K : Type} [Field K] [Fintype ι] [Fintype κ]
    (u : ι → K) (w : κ → K) (i : ι) (j : κ) (hij : u i * w j ≠ 0) :
    (Matrix.vecMulVec u w).rank = 1 := by
  refine le_antisymm (Matrix.rank_vecMulVec_le u w) ?_
  have hdet : ((Matrix.vecMulVec u w).submatrix (fun _ : Fin 1 => i)
      (fun _ : Fin 1 => j)).det ≠ 0 := by
    rw [Matrix.det_unique]
    simpa [Matrix.vecMulVec_apply] using hij
  have h := Matrix.rank_submatrix_le (Matrix.vecMulVec u w) (fun _ : Fin 1 => i)
    (fun _ : Fin 1 => j)
  rw [Matrix.rank_of_isUnit _ (Matrix.isUnit_iff_isUnit_det _ |>.mpr
    (isUnit_iff_ne_zero.mpr hdet))] at h
  simpa using h

theorem rank_spTrans_sub_one {n : ℕ} {F : Type} [Field F] {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0)
    {c : F} (hc : c ≠ 0) : (CaseM.spTrans v c - 1).rank = 1 := by
  have hsub : CaseM.spTrans v c - 1 = Matrix.vecMulVec (c • v) (v ᵥ* CaseM.spGram n F) := by
    change (1 + c • CaseM.spNil v) - 1 = Matrix.vecMulVec (c • v) (v ᵥ* CaseM.spGram n F)
    rw [Matrix.smul_vecMulVec]
    abel
  rw [hsub]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (CaseM.vecMul_spGram_ne_zero hv)
  refine timti_rank_vecMulVec_eq_one (c • v) (v ᵥ* CaseM.spGram n F) i j ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_ne_zero (mul_ne_zero hc hi) hj

theorem isSymplecticTransvectionIn_of_isTransGroup {n : ℕ} {F : Type} [Field F]
    {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) {T : Subgroup ↥(StatedSp n F)}
    (hT : CaseM.IsTransGroup v T) {x : ↥(StatedSp n F)} (hx : x ∈ T) (hx1 : x ≠ 1) :
    SevenK.IsSymplecticTransvectionIn n x := by
  obtain ⟨c, hc⟩ := (hT.1 x).1 hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine hx1 (SpExtras.mat_injective ?_)
    rw [hc, map_one]
    simp [CaseM.spTrans]
  unfold SevenK.IsSymplecticTransvectionIn
  rw [← SpExtras.mat_apply x, hc]
  exact rank_spTrans_sub_one hv hc0

theorem exists_equiv_sp_of_isTransGroup {H : Type} [Group H] {n : ℕ} {F : Type} [Field F]
    (Φ : ↥(StatedSp n F) →* H) (hΦ : Function.Bijective Φ) {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0)
    {T : Subgroup ↥(StatedSp n F)} (hT : CaseM.IsTransGroup v T) :
    ∃ e : H ≃* ↥(StatedSp n F), ∀ t ∈ T, t ≠ 1 → SevenK.IsSymplecticTransvectionIn n (e (Φ t)) := by
  refine ⟨(MulEquiv.ofBijective Φ hΦ).symm, fun t ht ht1 => ?_⟩
  have h1 : (MulEquiv.ofBijective Φ hΦ).symm (Φ t) = t := by
    rw [← MulEquiv.ofBijective_apply Φ hΦ t]
    exact MulEquiv.symm_apply_apply _ t
  rw [h1]
  exact isSymplecticTransvectionIn_of_isTransGroup hv hT ht ht1

end CFSG.LocalAnalysis.WeakClosure81.TimTI
