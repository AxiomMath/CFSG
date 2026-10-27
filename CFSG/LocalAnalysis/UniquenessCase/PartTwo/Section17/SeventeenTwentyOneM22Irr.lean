module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22Bound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G}

section Certified


theorem fixV_barSub_eq_bot_of_M22
    (hV : Hyp125 D V₀ V) (h17_20 : R17_20At D V₀ V)
    (h869 : F08.R869 D) (h127 : R127 D) (hC117 : C117 D V₀ V)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (c : Ctx17_17 D V₀ V L) (hN : (L.subgroupOf D.M).Normal)
    (hSp2 : IsSpor (Bar2 L) .M22) :
    fixV (barSub V₀ V hV.isElemAbelian L) = ⊥ := by
  classical
  have hnt : ¬ F08.Thin8 L := by
    obtain ⟨hm3, -, -⟩ := h17_20 L c
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV c.mem_calC hnt
    · exact barSub_ne_bot_of_not_thin hV hC117 c.mem_calC hnt
  have hcomp : F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) :=
    isComponentModO2_sup_pCoreOf_of_mem_calC c.mem_calC
  have hUK : UniqueMax D.M ((L ⊔ pCoreOf 2 D.M) ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D
      (sup_le ((le_sup_left : L ≤ L ⊔ pCoreOf 2 D.M).trans le_sup_left) le_sup_right)
      (sup_le (sup_le c.mem_calC.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) D.sylowM.le)
      (uniqueMax_sup_T_of_not_thin h869 c.mem_calC hnt)
  have hbar : barSub V₀ V hV.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) =
      barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) :=
    S18.barSub_conjClosure_sup_pCoreOf hV c.mem_calC.1.le
  have hH : barSub V₀ V hV.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) ≠ ⊥ := by
    rw [hbar]
    exact TwelveTwentyThree.barSub_conjClosure_ne_bot hV.isElemAbelian hL1
  rcases twelve_twentySix D h640 hFF hV hcomp hUK hH with hfix | ⟨-, hcl, -⟩
  · have h1 : fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ := by
      rwa [hbar] at hfix
    rwa [Inputs1719.conjClosure_eq_self_of_normal c.mem_calC.1.le hN] at h1
  · exfalso
    obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv_of_mem_calC c.mem_calC
    obtain ⟨f⟩ := hSp2
    exact not_classicalEvenAltG2Der_of_M22 ⟨e.trans f⟩ hcl

theorem iSup_irrSet_eq_top_of_M22
    (hV : Hyp125 D V₀ V) (h17_20 : R17_20At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (c : Ctx17_17 D V₀ V L) (hN : (L.subgroupOf D.M).Normal) :
    (⨆ I ∈ irrSet (barSub V₀ V hV.isElemAbelian L), I) = ⊤ := by
  classical
  have hnt : ¬ F08.Thin8 L := by
    obtain ⟨hm3, -, -⟩ := h17_20 L c
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV c.mem_calC hnt
    · exact barSub_ne_bot_of_not_thin hV hC117 c.mem_calC hnt
  have hLMb : barSub V₀ V hV.isElemAbelian L ≤ Mbar D.M V₀ V hV.isElemAbelian :=
    barSub_mono V₀ V hV.isElemAbelian c.mem_calC.1.le
  have hNbar : ((barSub V₀ V hV.isElemAbelian L).subgroupOf
      (Mbar D.M V₀ V hV.isElemAbelian)).Normal :=
    barSub_subgroupOf_mbar_normal hV.isElemAbelian c.mem_calC.1.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN)
  have hcomp : barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot hV c.mem_calC hL1
  have hXsup : barSub V₀ V hV.isElemAbelian L =
      ⨆ φ ∈ Mbar D.M V₀ V hV.isElemAbelian,
        (barSub V₀ V hV.isElemAbelian L).map (MulAut.conj φ).toMonoidHom := by
    have hconst : ∀ φ ∈ Mbar D.M V₀ V hV.isElemAbelian,
        (barSub V₀ V hV.isElemAbelian L).map (MulAut.conj φ).toMonoidHom =
          barSub V₀ V hV.isElemAbelian L := by
      intro φ hφ
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLMb).1 hNbar hφ)
    refine le_antisymm ?_ (iSup₂_le fun φ hφ => (hconst φ hφ).le)
    refine le_iSup₂_of_le (1 : MulAut (Vtil V₀ V hV.isElemAbelian)) (Subgroup.one_mem _) ?_
    rw [hconst 1 (Subgroup.one_mem _)]
  exact (twelve_seventeen D hx h61 h127 h1214 hV (barSub V₀ V hV.isElemAbelian L)
    hL1 hLMb hNbar (Or.inr ⟨_, hcomp, hXsup⟩)).1

theorem isIrrOn_barSub_of_M22
    (hRed : Inputs1719.K_M22ReducibleBound)
    (hV : Hyp125 D V₀ V) (h17_20 : R17_20At D V₀ V)
    (h869 : F08.R869 D) (h127 : R127 D) (hC117 : C117 D V₀ V)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h1214 : F12.R1214 D) (hKHex : Inputs1719.K_M22HexadPair)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (c : Ctx17_17 D V₀ V L) (hN : (L.subgroupOf D.M).Normal)
    (hspor : IsSpor (BarInf L) .M22)
    (hSp : IsSpor ↥(barSub V₀ V hV.isElemAbelian L) .M22)
    (hSp2 : IsSpor (Bar2 L) .M22) :
    IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥ := by
  classical
  by_contra hnot
  have hfix : fixV (barSub V₀ V hV.isElemAbelian L) = ⊥ :=
    fixV_barSub_eq_bot_of_M22 hV h17_20 h869 h127 hC117 h640 hFF c hN hSp2
  have hspan : (⨆ I ∈ irrSet (barSub V₀ V hV.isElemAbelian L), I) = ⊤ :=
    iSup_irrSet_eq_top_of_M22 hV h17_20 hx h61 h127 h1214 h869 hC117 c hN
  have hLMb : barSub V₀ V hV.isElemAbelian L ≤ Mbar D.M V₀ V hV.isElemAbelian :=
    barSub_mono V₀ V hV.isElemAbelian c.mem_calC.1.le
  have hNbar : ((barSub V₀ V hV.isElemAbelian L).subgroupOf
      (Mbar D.M V₀ V hV.isElemAbelian)).Normal :=
    barSub_subgroupOf_mbar_normal hV.isElemAbelian c.mem_calC.1.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN)
  have hsq : ∀ w : Vtil V₀ V hV.isElemAbelian, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian
  have hb : bBar L D.M V₀ V hV.isElemAbelian + 3 ≤ mBar D.M V₀ V hV.isElemAbelian :=
    hRed (W := Vtil V₀ V hV.isElemAbelian) hsq
      (Mbar D.M V₀ V hV.isElemAbelian) (barSub V₀ V hV.isElemAbelian L)
      hLMb hNbar hSp hfix hspan hnot
  have hm : mBar D.M V₀ V hV.isElemAbelian ≤ bBar L D.M V₀ V hV.isElemAbelian + 2 :=
    mBar_le_bBar_add_two_of_M22 hV c h17_20 hKHex hspor hsp3 hx h61 h63 h127 h1114
      h162 hTor h1482 h126 h111 h869 hC117
  omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
