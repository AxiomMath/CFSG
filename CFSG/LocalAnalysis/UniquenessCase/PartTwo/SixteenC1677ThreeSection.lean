module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSectionTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s15_inf_ker_kappa_eq_inf_fixV {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    wTil V₀ V h.isElemAbelian L ⊓
        (s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V
          h.isElemAbelian
          (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)).ker =
      wTil V₀ V h.isElemAbelian L ⊓
        fixV (lBar V₀ V h.isElemAbelian L) := by
  have hV := h.isElemAbelian
  have hker : (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
      (s15_Infra_le_v1Sub D.M V₀ V hV L)).ker =
      imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
    s15_semiBot_ker_kappa (v1Sub D.M V₀ V hV L) hV (s15_Infra_le_v1Sub D.M V₀ V hV L)
  rw [hker]
  have h1 : imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ≤ fixV (lBar V₀ V hV L) := by
    have h := s15_Core_imgTil_v1Sub_le_fixV h (m := 1) D.M.one_mem
    rwa [conjSubgroup_one] at h
  have h2 : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) ≤
      fixV (⨆ j : D.M, barSub V₀ V hV (conjSubgroup L (j : G))) := by
    rintro u hu
    obtain ⟨huU, huH⟩ := Subgroup.mem_inf.1 hu
    rw [CFSG.Quasithin.fixV_iSup]
    refine Subgroup.mem_iInf.2 fun m => ?_
    rw [mem_fixV] at huH ⊢
    intro x hx
    by_cases hm : barSub V₀ V hV (conjSubgroup L (m : G)) = barSub V₀ V hV L
    · have hx' : x ∈ barSub V₀ V hV L := by rwa [hm] at hx
      exact huH x hx'
    · have hne : (m : G) * (1 : G)⁻¹ ∉ nBar D.M V₀ V hV L := by
        rw [s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV D.M.one_mem m.2]
        simpa [conjSubgroup_one] using hm
      have hcomm := (s15_Kbar_commute_conj h D.M.one_mem m.2 hne).2
      have hUfix : wTil V₀ V hV L ≤ fixV (barSub V₀ V hV (conjSubgroup L (m : G))) := by
        rw [← commSub_eq_bot_iff]
        simpa [wTil, conjSubgroup_one] using hcomm
      exact (mem_fixV.1 (hUfix huU)) x hx
  have hcore : wTil V₀ V hV L ⊓
      fixV (⨆ j : D.M, barSub V₀ V hV (conjSubgroup L (j : G))) ≤
      imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
    have h := s15_Core_inf_fixV_le_imgTil_v1Sub h hL (1 : D.M)
    simpa [conjSubgroup_one] using h
  refine le_antisymm ?_ ?_
  · exact le_inf inf_le_left (inf_le_right.trans h1)
  · exact le_inf inf_le_left ((le_inf inf_le_left h2).trans hcore)

theorem s168e3_den_map_eq_bot {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) :
    (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)).map
      (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
        (s15_Infra_le_v1Sub D.M V₀ V hV L)) = ⊥ := by
  have hker := s15_inf_ker_kappa_eq_inf_fixV c.setting.hyp151 c.ne
  rw [Subgroup.map_eq_bot_iff]
  rw [← hker]
  exact inf_le_right

theorem s168e3_section_kappa_data {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) :
    Function.Surjective (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
        (s15_Infra_le_v1Sub D.M V₀ V hV L)) ∧
      ∃ θ : ↥(lBar V₀ V hV L) ≃* ↥(lStar D.M V₀ V hV L),
        (∀ (h : ↥(lBar V₀ V hV L)) (w : Vtil V₀ V hV),
          s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
              (s15_Infra_le_v1Sub D.M V₀ V hV L)
              ((h : MulAut (Vtil V₀ V hV)) w) =
            ((θ h : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L))
              (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
                (s15_Infra_le_v1Sub D.M V₀ V hV L) w)) ∧
        (wTil V₀ V hV L).map (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
          (s15_Infra_le_v1Sub D.M V₀ V hV L)) = wStar D.M V₀ V hV L ∧
        wTil V₀ V hV L ⊓ (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
          (s15_Infra_le_v1Sub D.M V₀ V hV L)).ker =
          wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) := by
  obtain ⟨ρ, hLmap, hκρ⟩ := s16e_two_kappa_equiv D c.std.h1217 c.setting.hyp151 hV
  have hHle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    s16e_two_lBar_le D c.setting.hyp151 hV
  have hHleS : lStar D.M V₀ V hV L ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    s16e_two_lStar_le D c.setting.hyp151 hV
  let θ : ↥(lBar V₀ V hV L) ≃* ↥(lStar D.M V₀ V hV L) :=
    ((Subgroup.subgroupOfEquivOfLe hHle).symm).trans
      ((MulEquiv.subgroupMap ρ ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV))).trans
        ((MulEquiv.subgroupCongr hLmap).trans (Subgroup.subgroupOfEquivOfLe hHleS)))
  refine ⟨s15_T7_kappa_surjective V₀ (v1Sub D.M V₀ V hV L) V hV
      (s15_Infra_le_v1Sub D.M V₀ V hV L), θ, ?_, ?_, ?_⟩
  · intro h w
    have hcoe : ((θ h : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L)) =
        ((ρ ⟨(h : MulAut (Vtil V₀ V hV)), hHle h.2⟩ :
          ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
          MulAut (vStar D.M V₀ V hV L)) := rfl
    rw [hcoe]
    exact hκρ ⟨(h : MulAut (Vtil V₀ V hV)), hHle h.2⟩ w
  · exact (s15_semiBot_wStar_eq_map c.setting.hyp151).symm
  · exact s15_inf_ker_kappa_eq_inf_fixV c.setting.hyp151 c.ne

theorem s168e3_realizes_map_of_kappa {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {Dm : FFModel} {I : Subgroup (Vtil V₀ V hV)}
    (hIU : I ≤ wTil V₀ V hV L)
    (hR : Dm.Realizes (lBar V₀ V hV L) I
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L))) :
    Dm.Realizes (lStar D.M V₀ V hV L)
      (I.map (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
        (s15_Infra_le_v1Sub D.M V₀ V hV L))) ⊥ := by
  obtain ⟨hsurj, θ, hequiv, -, hker⟩ := s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V)
    (L := L) (hV := hV) c
  have hIker : I ⊓ (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
        (s15_Infra_le_v1Sub D.M V₀ V hV L)).ker ≤
      wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) := by
    calc I ⊓ (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
          (s15_Infra_le_v1Sub D.M V₀ V hV L)).ker ≤
        wTil V₀ V hV L ⊓ (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
          (s15_Infra_le_v1Sub D.M V₀ V hV L)).ker := inf_le_inf_right _ hIU
      _ = wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) := hker
  have hZbot : (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)).map
      (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV
        (s15_Infra_le_v1Sub D.M V₀ V hV L)) = ⊥ :=
    s168e3_den_map_eq_bot c
  have h1 := realizes_map_of_surjective_of_inf_ker_le hR
    (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L))
    hsurj hIker θ.toMonoidHom θ.surjective hequiv
  rwa [hZbot] at h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
