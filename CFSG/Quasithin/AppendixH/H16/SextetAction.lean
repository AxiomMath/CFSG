module

public import CFSG.Quasithin.AppendixH.H16.SextetGroup

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc

theorem actsBy_sxT : ActsBy (rhoCd sxT_mem) sxTC := by
  rw [← sxTC_eq]
  exact actsBy_of_xorLin (xorLin_actC11 _) (rhoCd_toW sxT_mem hasArr_sxT)

theorem imgCd_sxGen_le_stabSub : imgCd sxGen ≤ stabSub US :=
  imgCd_closure_le (S := ({sxG1, sxG2, sxT} : Set (Equiv.Perm (Fin 24)))) (by
    rintro _ (rfl | rfl | rfl)
    · exact sxG1_mem
    · exact sxG2_mem
    · exact sxT_mem) (by
    rintro _ (rfl | rfl | rfl)
    · exact sxG1_stab
    · exact sxG2_stab
    · exact sxT_stab)

theorem rhoOf_sxT :
    B42Alt6.rhoOf usTheta sTP = resHom US ⟨rhoCd sxT_mem, sxT_stab⟩ :=
  rhoOf_eq sxT_stab actsBy_sxT (fun x hx => sxTC_lt x hx) th_t_ok

theorem autSub_imgCd_sxGen_le_range :
    autSub (imgCd sxGen) US ≤ (B42Alt6.rhoOf usTheta).range := by
  set T := (((B42Alt6.rhoOf usTheta).range.comap (resHom US)).map (stabSub US).subtype)
  have hT : imgCd sxGen ≤ T := by
    refine imgCd_closure_le (S := ({sxG1, sxG2, sxT} : Set (Equiv.Perm (Fin 24)))) (by
      rintro _ (rfl | rfl | rfl)
      · exact sxG1_mem
      · exact sxG2_mem
      · exact sxT_mem) ?_
    rintro _ (rfl | rfl | rfl)
    · refine ⟨⟨rhoCd sxG1_mem, sxG1_stab⟩, ⟨s1P, ?_⟩, rfl⟩
      exact rhoOf_eq sxG1_stab actsBy_sxG1 (fun x hx => sxCols_lt x (List.mem_append_left _ hx))
        fun m hm i => ((th_ok m hm).2.2.2.2 i).1
    · refine ⟨⟨rhoCd sxG2_mem, sxG2_stab⟩, ⟨s2P, ?_⟩, rfl⟩
      exact rhoOf_eq sxG2_stab actsBy_sxG2 (fun x hx => sxCols_lt x (List.mem_append_right _ hx))
        fun m hm i => ((th_ok m hm).2.2.2.2 i).2
    · refine ⟨⟨rhoCd sxT_mem, sxT_stab⟩, ⟨sTP, ?_⟩, rfl⟩
      exact rhoOf_sxT
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
  obtain ⟨g', hg', hgg'⟩ := hT hg
  rw [← show g' = g from Subtype.ext hgg']
  exact hg'

theorem range_le_autSub_imgCd_sxGen :
    (B42Alt6.rhoOf usTheta).range ≤ autSub (imgCd sxGen) US := by
  obtain ⟨-, hρ, -⟩ := lu_code_std (hS := card_stab_US_le)
  have hle : autSub (imgCd sxP0) US ≤ autSub (imgCd sxGen) US :=
    autSub_mono (Subgroup.map_mono (Subgroup.subgroupOf_mono AutPerm sxP0_le_gen)) US
  have hT : B42Alt6.rhoOf usTheta sTP ∈ autSub (imgCd sxGen) US := by
    rw [rhoOf_sxT]
    exact mem_autSub.2 ⟨⟨rhoCd sxT_mem, sxT_stab⟩, rhoCd_mem_imgCd sxT_mem sxT_mem_gen, rfl⟩
  have key : ∀ σ : Equiv.Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) →
      B42Alt6.rhoOf usTheta σ ∈ autSub (imgCd sxGen) US := by
    intro σ hσ
    have h1 : B42Alt6.rhoOf usTheta σ ∈
        (alternatingGroup (Fin 6)).map (B42Alt6.rhoOf usTheta) := ⟨σ, hσ, rfl⟩
    rw [hρ] at h1
    exact hle h1
  rintro φ ⟨σ, rfl⟩
  by_cases hs : Equiv.Perm.sign σ = 1
  · exact key σ (Equiv.Perm.mem_alternatingGroup.2 hs)
  · have hσ1 : Equiv.Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd h hs
      · exact h
    have hT1 : Equiv.Perm.sign sTP = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign sTP) with h | h
      · exact absurd h sign_sTP
      · exact h
    have hσalt : σ * sTP⁻¹ ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hσ1, hT1]
      norm_num
    have h2 : B42Alt6.rhoOf usTheta σ =
        B42Alt6.rhoOf usTheta (σ * sTP⁻¹) * B42Alt6.rhoOf usTheta sTP := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h2]
    exact Subgroup.mul_mem _ (key _ hσalt) hT

theorem autSub_imgCd_sxGen :
    autSub (imgCd sxGen) US = (B42Alt6.rhoOf usTheta).range :=
  le_antisymm autSub_imgCd_sxGen_le_range range_le_autSub_imgCd_sxGen

@[expose] noncomputable def sxRho : ↥sxGen →* MulAut W11 :=
  (rhoC11 AutPerm le_rfl).comp (Subgroup.inclusion sxGen_le_AutPerm)

theorem sxRho_apply (g : S24) (hg : g ∈ sxGen) :
    sxRho ⟨g, hg⟩ = rhoCd (sxGen_le_AutPerm hg) :=
  rfl

theorem sxRho_mem_imgCd (g : ↥sxGen) : sxRho g ∈ imgCd sxGen := by
  change rhoCd (sxGen_le_AutPerm g.2) ∈ imgCd sxGen
  exact rhoCd_mem_imgCd (sxGen_le_AutPerm g.2) g.2

theorem sxRho_mem_stabSub (g : ↥sxGen) : sxRho g ∈ stabSub US :=
  imgCd_sxGen_le_stabSub (sxRho_mem_imgCd g)

@[expose] noncomputable def sxResUS : ↥sxGen →* MulAut ↥US :=
  (resHom US).comp (MonoidHom.codRestrict sxRho (stabSub US) sxRho_mem_stabSub)

theorem sxResUS_apply (g : ↥sxGen) : sxResUS g = resHom US ⟨sxRho g, sxRho_mem_stabSub g⟩ := rfl

theorem sxResUS_mem_range (g : ↥sxGen) : sxResUS g ∈ (B42Alt6.rhoOf usTheta).range := by
  rw [sxResUS_apply]
  exact autSub_imgCd_sxGen_le_range
    (mem_autSub.2 ⟨⟨sxRho g, sxRho_mem_stabSub g⟩, sxRho_mem_imgCd g, rfl⟩)

@[expose] noncomputable def sxAct : ↥sxGen →* Equiv.Perm (Fin 6) :=
  (MonoidHom.ofInjective (B42Alt6.rhoOf_injective usTheta)).symm.toMonoidHom.comp
    (MonoidHom.codRestrict sxResUS (B42Alt6.rhoOf usTheta).range sxResUS_mem_range)

theorem rhoOf_sxAct (g : ↥sxGen) :
    B42Alt6.rhoOf usTheta (sxAct g) = resHom US ⟨sxRho g, sxRho_mem_stabSub g⟩ := by
  have h : sxAct g = (MonoidHom.ofInjective (B42Alt6.rhoOf_injective usTheta)).symm
      (MonoidHom.codRestrict sxResUS (B42Alt6.rhoOf usTheta).range sxResUS_mem_range g) := rfl
  rw [h]
  erw [MonoidHom.apply_ofInjective_symm]
  exact sxResUS_apply g

theorem sxAct_surjective :
    Function.Surjective sxAct := by
  intro σ
  have hmem : B42Alt6.rhoOf usTheta σ ∈ autSub (imgCd sxGen) US := by
    rw [autSub_imgCd_sxGen]
    exact ⟨σ, rfl⟩
  obtain ⟨g, hgmem, hg⟩ := mem_autSub.1 hmem
  rw [imgCd] at hgmem
  obtain ⟨τ, hτ, hfa⟩ := hgmem
  have hxg : sxRho ⟨(τ : S24), Subgroup.mem_subgroupOf.1 hτ⟩ = g.1 := by
    rw [sxRho_apply]
    exact hfa
  have hsub : (⟨sxRho ⟨(τ : S24), Subgroup.mem_subgroupOf.1 hτ⟩,
      sxRho_mem_stabSub ⟨(τ : S24), Subgroup.mem_subgroupOf.1 hτ⟩⟩ : stabSub US) = g :=
    Subtype.ext hxg
  refine ⟨⟨(τ : S24), Subgroup.mem_subgroupOf.1 hτ⟩, ?_⟩
  apply B42Alt6.rhoOf_injective usTheta
  rw [rhoOf_sxAct, hsub, hg]

theorem sxAct_eq_one_iff (g : ↥sxGen) : sxAct g = 1 ↔ ∀ u ∈ US, sxRho g u = u := by
  rw [← map_eq_one_iff (B42Alt6.rhoOf usTheta) (B42Alt6.rhoOf_injective usTheta),
    rhoOf_sxAct g, ← MonoidHom.mem_ker]
  erw [ker_resHom]
  erw [Subgroup.mem_subgroupOf]
  erw [mem_centSub]
  rfl

theorem sxAct_of_mem_sxKS (g : ↥sxGen) (hk : (g : S24) ∈ sxKS) : sxAct g = 1 := by
  rw [sxAct_eq_one_iff]
  intro u hu
  have h1 : sxRho g ∈ imgCd sxKS := by
    change rhoCd (sxGen_le_AutPerm g.2) ∈ imgCd sxKS
    exact rhoCd_mem_imgCd ((sxKS_le_P0.trans sxP0_le) hk) hk
  exact (mem_centSub.1 (imgCd_KS_le h1).2) u hu

end CFSG.ASVolI.H16
