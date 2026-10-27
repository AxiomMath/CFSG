module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Normal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Equiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem bBar_le_two_mul_of_is2F4
    {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h2F4 : Inputs1719.W4Lem4_17TwoF4N) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hfix : fixV (barSub V₀ V hV.isElemAbelian L) = ⊥)
    (hsimple : IsSimpleGroup (Bar2 L)) {n : ℕ}
    (h2F4L : CFSG.Quasithin.Is2F4 n (Bar2 L)) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ 2 * n := by
  have hV' := hV.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V hV' (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV' hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  obtain ⟨e⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV' hLstab h2 hL1 hsimple
  have h2F4' : CFSG.Quasithin.Is2F4 n ↥(barSub V₀ V hV' L) :=
    CFSG.Quasithin.Is2F4.of_mulEquiv e h2F4L
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
  have hsyl : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hV' D.T)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) := by
    have h := S17.isSylowIn_barSub_T_sup hV hLM
    rwa [s16c7_barSub_sup V₀ V hV' hLstab
      (D.sylowM.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀))] at h
  have hpow : ∀ w : Vtil V₀ V hV', w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV'
  have hfixne : fixV (barSub V₀ V hV' D.T) ≠
      fixV (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) :=
    fixV_ne_fixV_sup hpow hL1 hfix hsyl.isPGroup
  have hodd : Odd (Nat.card (Subgroup.center ↥(barSub V₀ V hV' L))) :=
    odd_card_center_of_mulEquiv_of_isSimpleGroup e hsimple hL.2.2.1
  have hTNbar : barSub V₀ V hV' D.T ≤ Subgroup.normalizer
      (barSub V₀ V hV' L : Set (MulAut (Vtil V₀ V hV'))) := hTbarM.trans hNM
  have hbound : bParam (barSub V₀ V hV' L)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) ≤ 2 * n :=
    Inputs1719.bParam_le_two_mul_of_is2F4_of_normal h2F4 hpow le_sup_left le_sup_right rfl
      hcomp hsyl hfixne hodd hTNbar h2F4'
  exact bBar_le_of_sup_bound hV hL hN hbound

theorem bBar_le_two_of_isTits
    {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hfix : fixV (barSub V₀ V hV.isElemAbelian L) = ⊥)
    (hsimple : IsSimpleGroup (Bar2 L)) (hTits : CFSG.Quasithin.IsTits (Bar2 L)) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ 2 := by
  have hV' := hV.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V hV' (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV' hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  obtain ⟨e⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV' hLstab h2 hL1 hsimple
  have hTits' : CFSG.Quasithin.IsTits ↥(barSub V₀ V hV' L) :=
    CFSG.Quasithin.IsTits.of_mulEquiv e hTits
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
  have hsyl : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hV' D.T)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) := by
    have h := S17.isSylowIn_barSub_T_sup hV hLM
    rwa [s16c7_barSub_sup V₀ V hV' hLstab
      (D.sylowM.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀))] at h
  have hpow : ∀ w : Vtil V₀ V hV', w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV'
  have hfixne : fixV (barSub V₀ V hV' D.T) ≠
      fixV (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) :=
    fixV_ne_fixV_sup hpow hL1 hfix hsyl.isPGroup
  have hodd : Odd (Nat.card (Subgroup.center ↥(barSub V₀ V hV' L))) :=
    odd_card_center_of_mulEquiv_of_isSimpleGroup e hsimple hL.2.2.1
  have hTNbar : barSub V₀ V hV' D.T ≤ Subgroup.normalizer
      (barSub V₀ V hV' L : Set (MulAut (Vtil V₀ V hV'))) := hTbarM.trans hNM
  have hbound : bParam (barSub V₀ V hV' L)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) ≤ 2 * 1 :=
    Inputs1719.bParam_le_two_of_isTits_of_normal hpow le_sup_left le_sup_right rfl hcomp
      hsyl hfixne hodd hTNbar hTits'
  simpa using bBar_le_of_sup_bound hV hL hN hbound

theorem bBar_le_four_mul_of_is3D4 {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h3D4 : Inputs1719.W4Lem4_17TrialityD4N) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hfix : fixV (barSub V₀ V hV.isElemAbelian L) = ⊥)
    (hsimple : IsSimpleGroup (Bar2 L)) {n : ℕ}
    (h3D4L : CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 (Bar2 L) n) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ 4 * n := by
  have hV' := hV.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V hV' (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV' hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  obtain ⟨e⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV' hLstab h2 hL1 hsimple
  have h3D4' : CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 ↥(barSub V₀ V hV' L) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e h3D4L
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
  have hsyl : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hV' D.T)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) := by
    have h := S17.isSylowIn_barSub_T_sup hV hLM
    rwa [s16c7_barSub_sup V₀ V hV' hLstab
      (D.sylowM.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀))] at h
  have hpow : ∀ w : Vtil V₀ V hV', w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV'
  have hfixne : fixV (barSub V₀ V hV' D.T) ≠
      fixV (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) :=
    fixV_ne_fixV_sup hpow hL1 hfix hsyl.isPGroup
  have hodd : Odd (Nat.card (Subgroup.center ↥(barSub V₀ V hV' L))) :=
    odd_card_center_of_mulEquiv_of_isSimpleGroup e hsimple hL.2.2.1
  have hTNbar : barSub V₀ V hV' D.T ≤ Subgroup.normalizer
      (barSub V₀ V hV' L : Set (MulAut (Vtil V₀ V hV'))) := hTbarM.trans hNM
  have hbound : bParam (barSub V₀ V hV' L)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) ≤ 4 * n :=
    Inputs1719.bParam_le_four_mul_of_is3D4_of_normal h3D4 hpow le_sup_left le_sup_right rfl
      hcomp hsyl hfixne hodd hTNbar h3D4'
  exact bBar_le_of_sup_bound hV hL hN hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
