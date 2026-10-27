module

public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22Red
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22Gen
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22SporMid
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22SporHS
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22SporJ4
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22QTK
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBMain

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin CFSG.Sporadic.Schreier CFSG.Blueprint

theorem inspBM22Cover_of
    (hLT : LTQTK) (hOrd : QTKOrdNoM22) (hM23 : M23InvCentOrd) (hM24 : M24InvCentOrd) :
    InspBM22Cover := by
  intro Yh _ _ Y r hY hq hQT hK hr hnc C hC hsn hCq hM
  have hqTop : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥Y) :=
    CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hq
  have hKTop : CFSG.SectionRank.IsKGroupCat ↥(⊤ : Subgroup ↥Y) :=
    CFSG.KCore.KGroupAllSimple.of_mulEquiv CFSG.SectionRank.catalog_isoInvariant hK
      Subgroup.topEquiv
  have hL : CFSG.SectionRank.QTK.QTKSimpleList (↥Y ⧸ Subgroup.center ↥Y) :=
    CFSG.SectionRank.QTK.qtkSimpleList_congr (quotCenterCongr Subgroup.topEquiv)
      (CFSG.SectionRank.QTK.CoverB.qtkSimpleList_of_cover (G := ↥Y) (Y := ⊤) hQT hqTop hKTop)
  obtain ⟨β, h2, h1, D, hD, hDsn, hDq, hDM⟩ :=
    exists_invol_aut_of_component Y r hY hq hr hnc C hC hsn hCq hM
  obtain ⟨eD⟩ := hDM
  have hφ : Function.Surjective (eD.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥D))) :=
    eD.surjective.comp QuotientGroup.mk_surjective
  have hdvd : 443520 ∣ Nat.card (fixSub β) := by
    have hM22 : Nat.card (NativeSporadic.Carrier .M22) = 443520 :=
      CFSG.Sporadic.Schreier.m22_card
    have hD22 : 443520 ∣ Nat.card ↥D := by
      rw [← hM22]
      exact Subgroup.card_dvd_of_surjective hφ
    have hle : D ≤ fixSub β := fun x hx => mem_fixSub.2 (hD x hx)
    have hDF : Nat.card ↥D ∣ Nat.card ↥(fixSub β) := by
      have := Subgroup.card_subgroup_dvd_card (D.subgroupOf (fixSub β))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
    exact hD22.trans hDF
  by_cases hsix : ∃ s : TauCeti.SporadicName,
      (s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .HS ∨ s = .McL ∨ s = .J4) ∧
        Nonempty ((↥Y ⧸ Subgroup.center ↥Y) ≃* NativeSporadic.Carrier s)
  · obtain ⟨s, hs, ⟨e⟩⟩ := hsix
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact m22_fixSub_card_not_dvd _ e β h1 hdvd
    · exact m23_fixSub_card_not_dvd hM23 _ e β h2 h1 hdvd
    · exact m24_fixSub_card_not_dvd hM24 _ e β h2 h1 hdvd
    · exact hs_fixSub_card_not_dvd _ e β h2 h1 hdvd
    · exact mcl_fixSub_card_not_dvd _ e β h2 h1 hdvd
    · exact (j4_no_component_fixSub _ e β h2 h1 D hD hDsn hDq)
  · exact prop3_generic hLT hOrd hL (fun s hs hiso => hsix ⟨s, hs, hiso⟩) D
      (eD.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥D))) hφ

end CFSG.Quasithin.H13.Ch4

end
