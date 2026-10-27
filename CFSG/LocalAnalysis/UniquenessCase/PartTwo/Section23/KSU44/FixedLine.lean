module

public import CFSG.Quasithin.H13.U4ParCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par

private lemma sElt_mem_hypUnitriangular_S04 {m : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 m K} {x y c : K} (hc : SAdm h x y c) :
    sElt h hc ∈ hypUnitriangular h 2 0 := by
  rw [mem_hypUnitriangular, coe_sElt]
  refine ⟨?_, fun a => ?_⟩
  · intro i j hij
    rcases ix_cases i with rfl | rfl | rfl | rfl <;>
      rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      simp_all [sMat_apply, one_apply]
  · rcases ix_cases a with rfl | rfl | rfl | rfl <;>
      simp [sMat_apply, one_apply]

private lemma mulVec_single_ie1_eq_self_S04 {m : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 m K} {g : hypSU h 2 0} (hg : g ∈ hypUnitriangular h 2 0) :
    ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
      (Pi.single ie1 1 : HypIndex 2 0 → K) = Pi.single ie1 1 := by
  funext a
  rw [mulVec_single_one, col_apply]
  have htri := (mem_hypUnitriangular.mp hg).1
  have hdiag := (mem_hypUnitriangular.mp hg).2
  rcases ix_cases a with rfl | rfl | rfl | rfl
  · rw [hdiag ie1]; simp
  · rw [htri (by simp [fullPos_ie1, fullPos_ie2])]; simp
  · rw [htri (by simp [fullPos_ie1, fullPos_if1])]; simp
  · rw [htri (by simp [fullPos_ie1, fullPos_if2])]; simp

private lemma sMat_one_zero_zero_mulVec_ie2_S04 {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (v : Ix → K) :
    (sMat h 1 0 0 *ᵥ v) ie2 = v ie2 + v if1 := by
  rw [mulVec, dotProduct, sum_ix]
  simp [sMat_apply, one_apply]

private lemma sMat_one_zero_zero_mulVec_ie1_S04 {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (v : Ix → K) :
    (sMat h 1 0 0 *ᵥ v) ie1 = v ie1 + v if2 := by
  rw [mulVec, dotProduct, sum_ix]
  simp [sMat_apply, one_apply]

private lemma sMat_zero_one_zero_mulVec_ie1_S04 {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (v : Ix → K) :
    (sMat h 0 1 0 *ᵥ v) ie1 = v ie1 + v ie2 := by
  rw [mulVec, dotProduct, sum_ix]
  simp [sMat_apply, one_apply]

theorem fixed_hypUnitriangular_iff {m : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 m K)
    (v : HypIndex 2 0 → K) :
    (∀ g ∈ hypUnitriangular hK 2 0,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = v) ↔
      ∃ c : K, v = c • (Pi.single ie1 1 : HypIndex 2 0 → K) := by
  constructor
  · intro hfix
    have hmem₁ := sElt_mem_hypUnitriangular_S04 (sAdm_x_zero hK 1)
    have hmem₂ := sElt_mem_hypUnitriangular_S04 (sAdm_zero_y hK 1)
    have h1 : sMat hK 1 0 0 *ᵥ v = v := by
      have := hfix (sElt hK (sAdm_x_zero hK 1)) hmem₁
      rwa [coe_sElt] at this
    have h2 : sMat hK 0 1 0 *ᵥ v = v := by
      have := hfix (sElt hK (sAdm_zero_y hK 1)) hmem₂
      rwa [coe_sElt] at this
    have hv_f1 : v if1 = 0 := by
      have h := congrFun h1 ie2
      rw [sMat_one_zero_zero_mulVec_ie2_S04] at h
      exact add_left_cancel (a := v ie2) (by simpa using h)
    have hv_f2 : v if2 = 0 := by
      have h := congrFun h1 ie1
      rw [sMat_one_zero_zero_mulVec_ie1_S04] at h
      exact add_left_cancel (a := v ie1) (by simpa using h)
    have hv_e2 : v ie2 = 0 := by
      have h := congrFun h2 ie1
      rw [sMat_zero_one_zero_mulVec_ie1_S04] at h
      exact add_left_cancel (a := v ie1) (by simpa using h)
    refine ⟨v ie1, ?_⟩
    funext a
    rcases ix_cases a with rfl | rfl | rfl | rfl
    · simp
    · rw [hv_e2]; simp
    · rw [hv_f1]; simp
    · rw [hv_f2]; simp
  · rintro ⟨c, rfl⟩ g hg
    rw [mulVec_smul, mulVec_single_ie1_eq_self_S04 hg]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
