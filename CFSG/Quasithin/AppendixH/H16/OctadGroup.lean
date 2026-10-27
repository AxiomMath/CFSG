module

public import CFSG.Quasithin.AppendixH.H16.OctadMask
public import CFSG.Quasithin.AppendixH.Common.OctadPtStabCard

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

@[expose] def octG1Arr : Array ℕ :=
  #[1, 2, 5, 7, 0, 4, 3, 6, 14, 19, 18, 15, 9, 20, 21, 8, 12, 17, 16, 13, 11, 22, 23, 10]

@[expose] def octG1Inv : Array ℕ :=
  #[4, 0, 1, 6, 5, 2, 7, 3, 15, 12, 23, 20, 16, 19, 8, 11, 18, 17, 10, 9, 13, 14, 21, 22]

@[expose] def octG2Arr : Array ℕ :=
  #[1, 7, 5, 0, 3, 2, 4, 6, 19, 10, 16, 9, 13, 20, 14, 23, 18, 11, 17, 8, 12, 21, 15, 22]

@[expose] def octG2Inv : Array ℕ :=
  #[3, 0, 5, 4, 6, 2, 7, 1, 19, 11, 9, 17, 20, 12, 14, 22, 10, 18, 16, 8, 13, 21, 23, 15]

theorem octG1_ok : InvPairOK 24 octG1Arr octG1Inv = true := by decide +kernel

theorem octG2_ok : InvPairOK 24 octG2Arr octG2Inv = true := by decide +kernel

theorem octG1_aut : autArrOK octG1Arr octG1Inv = true := by decide +kernel

theorem octG2_aut : autArrOK octG2Arr octG2Inv = true := by decide +kernel

@[expose] noncomputable def octG1 : Equiv.Perm (Fin 24) := permOfArr 24 octG1Arr octG1Inv octG1_ok

@[expose] noncomputable def octG2 : Equiv.Perm (Fin 24) := permOfArr 24 octG2Arr octG2Inv octG2_ok

theorem hasArr_octG1 : HasArr octG1 octG1Arr := hasArr_permOfArr octG1_ok

theorem hasArr_octG2 : HasArr octG2 octG2Arr := hasArr_permOfArr octG2_ok

theorem octG1_mem : octG1 ∈ AutPerm := mem_AutPerm_of_arr octG1_ok octG1_aut

theorem octG2_mem : octG2 ∈ AutPerm := mem_AutPerm_of_arr octG2_ok octG2_aut

theorem smul_octad0_eq_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a)
    (h : ∀ j < 24, (j < 8 ↔ a[j]! < 8)) : σ • octad0 = octad0 := by
  refine Finset.ext fun i => ?_
  rw [smul_finset_eq_map, Finset.mem_map_equiv]
  simp only [octad0, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : (σ (σ.symm i) : ℕ) = a[(σ.symm i : ℕ)]! := ha (σ.symm i)
  rw [Equiv.apply_symm_apply] at h1
  have h2 := h (σ.symm i : ℕ) (σ.symm i).2
  rw [← h1] at h2
  exact h2

theorem octG1_mem_octStab : octG1 ∈ octStab octad0 :=
  mem_octStab_iff.2 ⟨octG1_mem, smul_octad0_eq_of_arr hasArr_octG1 (by decide +kernel)⟩

theorem octG2_mem_octStab : octG2 ∈ octStab octad0 :=
  mem_octStab_iff.2 ⟨octG2_mem, smul_octad0_eq_of_arr hasArr_octG2 (by decide +kernel)⟩

@[expose] def octG1C : List ℕ := [1353, 1354, 1065, 1586, 1073, 1300, 459, 356, 1289, 1044, 1051]

@[expose] def octG2C : List ℕ := [361, 362, 1624, 87, 1612, 1665, 410, 1798, 1887, 532, 27]

theorem octG1C_eq : matOf 11 (actC11 octG1Arr) = octG1C := by decide +kernel

theorem octG2C_eq : matOf 11 (actC11 octG2Arr) = octG2C := by decide +kernel

theorem actsBy_octG1 : ActsBy (rhoCd octG1_mem) octG1C := by
  rw [← octG1C_eq]
  exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW octG1_mem hasArr_octG1)

theorem actsBy_octG2 : ActsBy (rhoCd octG2_mem) octG2C := by
  rw [← octG2C_eq]
  exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW octG2_mem hasArr_octG2)

theorem octStab_octad0_le_AutPerm : octStab octad0 ≤ AutPerm := inf_le_left

theorem fixO_le_octStab_octad0 : fixO ≤ octStab octad0 := by
  rw [← octFix_octad0]
  exact octFix_le_octStab octad0

theorem imgCd_fixO_normal :
    ∀ g ∈ imgCd (octStab octad0), ∀ k ∈ imgCd fixO, g * k * g⁻¹ ∈ imgCd fixO := by
  have hN : octStab octad0 ≤ Subgroup.normalizer (fixO : Set (Equiv.Perm (Fin 24))) := by
    rw [← octFix_octad0]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (octFix_le_octStab octad0)).1
      (normal_octFix octad0)
  intro g hg k hk
  have hmem := imgCd_le_normalizer (Γ := octStab octad0) (Δ := fixO) hN hg
  exact (Subgroup.mem_normalizer_iff.1 hmem k).1 hk

theorem isActsInv_octV1 : IsActsInv (actsOnModule (imgCd (octStab octad0))) octV1 := by
  rintro f ⟨y, hy, rfl⟩ v hv
  rw [← fixV_imgCd_fixO] at hv ⊢
  intro k hk
  have h1 : y⁻¹ ∈ imgCd (octStab octad0) := Subgroup.inv_mem _ hy
  have hmem : y⁻¹ * k * y ∈ imgCd fixO := by
    have h := imgCd_fixO_normal y⁻¹ h1 k hk
    simpa using h
  have hconj : y⁻¹ (k (y v)) = v := by
    have h := (mem_fixV.1 hv) (y⁻¹ * k * y) hmem
    simpa using h
  change k (y v) = y v
  calc k (y v) = y (y⁻¹ (k (y v))) := (MulEquiv.apply_symm_apply y _).symm
    _ = y v := by rw [hconj]

theorem isActsInv_octV5 : IsActsInv (actsOnModule (imgCd (octStab octad0))) octV5 := by
  rintro f ⟨y, hy, rfl⟩ w hw
  rw [← commV_imgCd_fixO] at hw ⊢
  show y w ∈ CFSG.Quasithin.commV (imgCd fixO)
  rw [CFSG.Quasithin.commV] at hw ⊢
  refine Subgroup.closure_induction
    (p := fun z _ => y z ∈ Subgroup.closure
      ({w : W11 | ∃ x ∈ imgCd fixO, ∃ v : W11, x v * v⁻¹ = w})) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨x', hx', v, rfl⟩
    exact Subgroup.subset_closure
      ⟨y * x' * y⁻¹, imgCd_fixO_normal y hy x' hx', y v, by simp [mul_assoc, map_inv]⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b ha hb iha ihb
    rw [map_mul]
    exact Subgroup.mul_mem _ iha ihb
  · intro a ha iha
    rw [map_inv]
    exact Subgroup.inv_mem _ iha

end CFSG.ASVolI.H16
