module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SporadicNotClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Nine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem bBar_le_two_of_isSpor_HS {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h119 : Inputs1719.W4Lem11_9b) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hfix : fixV (barSub V₀ V hV.isElemAbelian L) = ⊥)
    (hHS : IsSpor (Bar2 L) .HS) (hsimple : IsSimpleGroup (Bar2 L)) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ 2 := by
  have hV' := hV.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V hV' (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV' hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  obtain ⟨e⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV' hLstab h2 hL1 hsimple
  have hHS' : IsSpor ↥(barSub V₀ V hV' L) .HS := by
    obtain ⟨f⟩ := hHS
    exact ⟨e.symm.trans f⟩
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hcompM : IsComponentOf (barSub V₀ V hV' L) (Mbar D.M V₀ V hV') :=
    barSub_mem_compBar_of_ne_bot hV hL hL1
  have hLbarM : barSub V₀ V hV' L ≤ Mbar D.M V₀ V hV' := barSub_mono V₀ V hV' hLM
  have hTbarM : barSub V₀ V hV' D.T ≤ Mbar D.M V₀ V hV' :=
    barSub_mono V₀ V hV' D.sylowM.le
  have hNM : Mbar D.M V₀ V hV' ≤ Subgroup.normalizer
      (barSub V₀ V hV' L : Set (MulAut (Vtil V₀ V hV'))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbarM).1
      (barSub_subgroupOf_mbar_normal hV' hLM hMN)
  have hcomp : IsComponentOf (barSub V₀ V hV' L)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) :=
    isComponentOf_sup_of_normal hLbarM hNM hTbarM hcompM
  have hnorm : ((barSub V₀ V hV' L).subgroupOf
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((sup_le hLbarM hTbarM).trans hNM)
  have hsyl : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hV' D.T)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) := by
    have h := S17.isSylowIn_barSub_T_sup hV hLM
    rwa [s16c7_barSub_sup V₀ V hV' hLstab
      (D.sylowM.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀))] at h
  have hpow : ∀ w : Vtil V₀ V hV', w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV'
  have hfixne : fixV (barSub V₀ V hV' D.T) ≠
      fixV (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) :=
    fixV_ne_fixV_sup hpow hL1 hfix hsyl.isPGroup
  have hbound : bParam (barSub V₀ V hV' L)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) ≤ 2 :=
    h119 (Vtil V₀ V hV') hpow (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) (barSub V₀ V hV' L)
      (barSub V₀ V hV' D.T) le_sup_left le_sup_right rfl hnorm hcomp hsyl hHS' hfixne
  exact bBar_le_of_sup_bound hV hL hN hbound

section OrderCertificates


theorem b17_21Bound_holds
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h4128 : W4Lem12_8) (h869 : F08.R869 D) (h117 : C117 D V₀ V)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg) (h77 : Inputs1719.W4Lem7_7)
    (h119 : Inputs1719.W4Lem11_9)
    (hrowHS : Inputs1719.W4Thm11_1RowM .HS) (hrowRu : Inputs1719.W4Thm11_1Row .Ru) :
    B17_21Bound D V₀ V hV := by
  intro L hL hN _ hsp
  rcases hsp with hs | hs
  · have hs2 : IsSpor (Bar2 L) .HS :=
      isSpor_bar2_of_isSpor_barInf hL CFSG.SectionRank.HS_perfect_odd_cover_trivial hs
    have hnt : ¬ F08.Thin8 L :=
      not_thin8_of_two_le_pRank Nat.prime_three (by norm_num)
        (two_le_pRank_of_bar2 Nat.prime_three (by norm_num) (two_le_pRank_three_of_isSpor_HS hs2))
    have hne := barSub_ne_bot_of_not_thin hV h117 hL hnt
    have hfix := fixV_barSub_eq_bot_of_not_classical D h869 h127 h640 hFF hV hL hN hnt
      (not_classicalEvenAltG2Der_of_isSpor_HS hs2)
    have hsimple : IsSimpleGroup (Bar2 L) := by
      obtain ⟨e⟩ := hs2
      exact e.isSimpleGroup_congr.mpr CFSG.Sporadic.HS.isSimpleGroup_HS
    have hb := bBar_le_two_of_isSpor_HS hV (Inputs1719.w4Lem11_9b_of_w4Lem11_9 h119) hL hN hne
      hfix hs2 hsimple
    have hm := tableM_le_mBar D hx h61 h127 h1214 h4128 hV hL hne hrowHS hs
      (not_lieModel_psl_two_of_isSpor_HS hs)
    simp only [Inputs1719.tableM] at hm
    omega
  · have hs2 : IsSpor (Bar2 L) .Ru :=
      isSpor_bar2_of_isSpor_barInf hL CFSG.SectionRank.Ru_perfect_odd_cover_trivial hs
    have hne := barSub_ne_bot_of_two_le_pRank_bar2 hV h117 hL (two_le_pRank_three_of_isSpor_Ru hs2)
    have hb := bBar_le_tableA_of_normal hV h77 hrowRu hL hN hs
    have hm := tableM_le_mBar D hx h61 h127 h1214 h4128 hV hL hne hrowRu.rowM hs
      (not_lieModel_psl_two_of_isSpor_Ru hs)
    simp only [Inputs1719.tableA, Inputs1719.tableM] at hb hm
    omega

end OrderCertificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
