module

public import CFSG.Quasithin.AppendixH.H16.MaskSup
public import CFSG.Quasithin.AppendixH.H16.OctadConj
public import CFSG.Quasithin.AppendixH.H16.OctadFlag
public import CFSG.Quasithin.AppendixH.H16.OctadQuad
public import CFSG.Quasithin.AppendixH.H16.SextetO23
public import CFSG.Quasithin.AppendixH.H16.SextetV10
public import CFSG.Quasithin.AppendixH.Common.OctadStd

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def flag4Basis : List ℕ := [3, 333, 524, 1024]

@[expose] def oct6Basis : List ℕ := 333 :: oct5Basis

theorem flag4Basis_lt : ∀ a ∈ flag4Basis, a < 2 ^ 11 := by decide

theorem oct6Basis_lt : ∀ a ∈ oct6Basis, a < 2 ^ 11 := by decide

theorem oct6_nodup : (combos oct6Basis).Nodup := by decide

private theorem koFour_conj :
    cArr (cArr flagInv (koArr 4)) flagArr = wArr ((List.range 6).map ks6Arr) [2] := by
  decide +kernel

private theorem koTen_conj :
    cArr (cArr flagInv (koArr 10)) flagArr = wArr ((List.range 6).map ks6Arr) [0, 1, 2, 3, 4, 5] := by
  decide +kernel

private theorem fix_koFour_koTen : ∀ m < 2 ^ 11,
    actC11 (koArr 4) m = m → actC11 (koArr 10) m = m → m ∈ combos flag4Basis := by
  decide +kernel

private theorem flag_img_uS : ∀ m ∈ combos uSBasis, actC11 flagArr m ∈ combos flag4Basis := by
  decide +kernel

private theorem flag_img_uS' : ∀ m ∈ combos flag4Basis,
    ∃ m' ∈ combos uSBasis, actC11 flagArr m' = m := by
  decide +kernel

private theorem octQmask_oct6 : ∀ m ∈ combos oct6Basis, octQmask (actM liftCCols m) = 0 := by
  decide +kernel

private theorem flag4_sub_oct6 : ∀ m ∈ combos flag4Basis, m ∈ combos oct6Basis := by
  decide +kernel

private theorem imgCd_mono {A B : Subgroup (Equiv.Perm (Fin 24))} (h : A ≤ B) :
    imgCd A ≤ imgCd B :=
  Subgroup.map_mono (f := rhoC11 AutPerm le_rfl) (Subgroup.subgroupOf_mono AutPerm h)

theorem KY_flagSextet :
    KY M24g flagSextet = conjSubg flagPerm sxKS := by
  rw [flagSextet, KY_smul_of_mem flagPerm_mem, KY, MY_stdSextet_eq, pCoreOf_two_sxGen]

theorem fixV_imgCd_KY_flagSextet :
    fixV (imgCd (KY M24g flagSextet)) = maskSub 11 flag4Basis := by
  have hflag : flagPerm ∈ AutPerm := flagPerm_mem
  have hg : ActsBy (rhoCd hflag) (matOf 11 (actC11 flagArr)) :=
    actsBy_of_xorLin (xorLin_actC11 flagArr) (rhoCd_toW hflag hasArr_flagPerm)
  have hlist : uSBasis.map (actM (matOf 11 (actC11 flagArr))) = uSBasis.map (actC11 flagArr) := by
    refine List.map_congr_left fun m hm => ?_
    exact actM_matOf (xorLin_actC11 flagArr) 11 m (uSBasis_lt m hm)
  rw [KY_flagSextet, fixV_imgCd_conjSubg hflag (sxKS_le_sxGen.trans sxGen_le_AutPerm)]
  have hfix : fixV (imgCd sxKS) = maskSub 11 uSBasis := fixV_imgCd_sxKS
  rw [hfix]
  show (maskSub 11 uSBasis).map (rhoCd hflag).toMonoidHom = maskSub 11 flag4Basis
  rw [CFSG.Quasithin.H.Parab.maskSub_map hg uSBasis, hlist]
  apply maskSub_eq_of_combos
  · intro m hm
    rw [CFSG.Quasithin.H.Parab.combos_map (xorLin_actC11 flagArr)] at hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
    exact flag_img_uS m' hm'
  · intro m hm
    rw [CFSG.Quasithin.H.Parab.combos_map (xorLin_actC11 flagArr)]
    exact List.mem_map.2 (flag_img_uS' m hm)

theorem koPerm_four_mem_KY_flagSextet :
    koPerm 4 ∈ KY M24g flagSextet := by
  rw [KY_flagSextet, mem_conjSubg_iff]
  have h1 : HasArr (flagPerm⁻¹ * koPerm 4 * flagPerm)
      (cArr (cArr flagInv (koArr 4)) flagArr) :=
    hasArr_mul (hasArr_mul (hasArr_permOfArr_inv flag_ok) (hasArr_permOfArr (koArr_ok 4).1))
      hasArr_flagPerm
  rw [koFour_conj] at h1
  rw [perm_eq_of_hasArr h1 (hasArr_wPerm hasArr_ksList [2])]
  exact wPerm_ksList_mem [2]

theorem koPerm_ten_mem_KY_flagSextet :
    koPerm 10 ∈ KY M24g flagSextet := by
  rw [KY_flagSextet, mem_conjSubg_iff]
  have h1 : HasArr (flagPerm⁻¹ * koPerm 10 * flagPerm)
      (cArr (cArr flagInv (koArr 10)) flagArr) :=
    hasArr_mul (hasArr_mul (hasArr_permOfArr_inv flag_ok) (hasArr_permOfArr (koArr_ok 10).1))
      hasArr_flagPerm
  rw [koTen_conj] at h1
  rw [perm_eq_of_hasArr h1 (hasArr_wPerm hasArr_ksList [0, 1, 2, 3, 4, 5])]
  exact wPerm_ksList_mem [0, 1, 2, 3, 4, 5]

theorem fixV_imgCd_KY_octad0_inf_flagSextet :
    fixV (imgCd (KY M24g octad0 ⊓ KY M24g flagSextet)) = maskSub 11 flag4Basis := by
  have hKO : KY M24g octad0 = fixO := by
    rw [KY, show MY M24g octad0 = octStab octad0 from rfl]
    exact pCoreOf_octStab_octad0
  have h4O : koPerm 4 ∈ KY M24g octad0 := by
    rw [hKO]; exact (mem_fixO_iff _).2 ⟨4, rfl⟩
  have h4S : koPerm 4 ∈ KY M24g flagSextet := koPerm_four_mem_KY_flagSextet
  have h10O : koPerm 10 ∈ KY M24g octad0 := by
    rw [hKO]; exact (mem_fixO_iff _).2 ⟨10, rfl⟩
  have h10S : koPerm 10 ∈ KY M24g flagSextet := koPerm_ten_mem_KY_flagSextet
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
    have h4img : rhoCd (koPerm_mem_mog22 4).1.1 ∈
        imgCd (KY M24g octad0 ⊓ KY M24g flagSextet) :=
      rhoCd_mem_imgCd (koPerm_mem_mog22 4).1.1 ⟨h4O, h4S⟩
    have h10img : rhoCd (koPerm_mem_mog22 10).1.1 ∈
        imgCd (KY M24g octad0 ⊓ KY M24g flagSextet) :=
      rhoCd_mem_imgCd (koPerm_mem_mog22 10).1.1 ⟨h10O, h10S⟩
    have h4 : actC11 (koArr 4) m = m :=
      toW_inj (actC11_lt (koArr 4) m) hm
        ((rhoCd_toW (koPerm_mem_mog22 4).1.1 (hasArr_permOfArr (koArr_ok 4).1) m).symm.trans
          ((mem_fixV.1 hx) _ h4img))
    have h10 : actC11 (koArr 10) m = m :=
      toW_inj (actC11_lt (koArr 10) m) hm
        ((rhoCd_toW (koPerm_mem_mog22 10).1.1 (hasArr_permOfArr (koArr_ok 10).1) m).symm.trans
          ((mem_fixV.1 hx) _ h10img))
    exact (toW_mem_maskSub_iff_of_lt flag4Basis_lt hm).2 (fix_koFour_koTen m hm h4 h10)
  · rw [← fixV_imgCd_KY_flagSextet]
    have himg : imgCd (KY M24g octad0 ⊓ KY M24g flagSextet) ≤ imgCd (KY M24g flagSextet) :=
      imgCd_mono inf_le_right
    exact fun _ hv φ hφ => hv φ (himg hφ)

theorem fixV_flagSextet_eq_fixV_inf :
    fixV (imgCd (KY M24g flagSextet)) = fixV (imgCd (KY M24g octad0 ⊓ KY M24g flagSextet)) := by
  rw [fixV_imgCd_KY_flagSextet, fixV_imgCd_KY_octad0_inf_flagSextet]

theorem fixV_flagSextet_sup_octV5 :
    fixV (imgCd (KY M24g flagSextet)) ⊔ octV5 = maskSub 11 oct6Basis := by
  have h333 : ∀ m ∈ combos [333], m ∈ combos flag4Basis := by
    intro m hm
    have h : m = 0 ∨ m = 333 := by simpa [combos] using hm
    rcases h with rfl | rfl
    · exact zero_mem_combos _
    · exact mem_combos_of_mem (by simp [flag4Basis])
  have h6 : maskSub 11 oct6Basis = maskSub 11 oct5Basis ⊔ maskSub 11 [333] := by
    rw [oct6Basis, maskSub_cons]
  rw [fixV_imgCd_KY_flagSextet, octV5, h6]
  apply le_antisymm
  · apply sup_le
    · rw [← h6]
      exact maskSub_mono_of_combos flag4_sub_oct6
    · exact le_sup_left
  · apply sup_le
    · exact le_sup_right
    · exact (maskSub_mono_of_combos h333).trans le_sup_left

theorem rk_fixV_flagSextet_sup_octV5 :
    rk ↥(fixV (imgCd (KY M24g flagSextet)) ⊔ octV5) = 6 := by
  rw [fixV_flagSextet_sup_octV5, rk_maskSub oct6Basis_lt oct6_nodup]
  rfl

theorem octQ_eq_zero_of_mem_fixV_flagSextet_sup_octV5 :
    ∀ x ∈ fixV (imgCd (KY M24g flagSextet)) ⊔ octV5, octQ x = 0 := by
  rw [fixV_flagSextet_sup_octV5]
  intro x hx
  obtain ⟨m, hm, rfl⟩ := hx
  rw [octQ_toW m, octQmask_oct6 m hm, Nat.cast_zero]

end CFSG.ASVolI.H16
