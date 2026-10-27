module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SporadicNotClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem b17_18Bound_holds (D : Data G) (V₀ V : Subgroup G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h4128 : W4Lem12_8) (h117 : C117 D V₀ V) (h77 : Inputs1719.W4Lem7_7)
    (hrow : Inputs1719.W4Thm11_1Row .ONan) : B17_18Bound D V₀ V := by
  intro hV L c hm3 _ hN hs
  have hb := bBar_conjClosure_le_tableA hV h77 hrow c.mem_calC hs
  have hnt : ¬ F08.Thin8 L := by
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [Inputs1719.conjClosure_eq_self_of_normal c.mem_calC.1.le hN] at hm3
    omega
  have hne := barSub_ne_bot_of_not_thin hV h117 c.mem_calC hnt
  have hm := tableM_le_mBar D hx h61 h127 h1214 h4128 hV c.mem_calC hne hrow.rowM hs
    (not_lieModel_psl_two_of_isSpor_ONan hs)
  simp only [Inputs1719.tableA, Inputs1719.tableM] at hb hm
  omega

theorem b17_19Bound_holds (D : Data G) (V₀ V : Subgroup G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h4128 : W4Lem12_8) (h117 : C117 D V₀ V) (h77 : Inputs1719.W4Lem7_7)
    (hrow : Inputs1719.W4Thm11_1Row .J1) : B17_19Bound D V₀ V := by
  intro hV L c hJ _ hU
  have hs : IsSpor (BarInf L) .J1 :=
    isSpor_barInf_of_isSpor_bar2 c.mem_calC CFSG.Sporadic.J1.isSimpleGroup_J1 hJ
  have hb := bBar_conjClosure_le_tableA hV h77 hrow c.mem_calC hs
  have hne := barSub_ne_bot_of_uniqueMax h127 hV h117 c.mem_calC hU
  have hm := tableM_le_mBar D hx h61 h127 h1214 h4128 hV c.mem_calC hne hrow.rowM hs
    (not_lieModel_psl_two_of_isSpor_J1 hs)
  simp only [Inputs1719.tableA, Inputs1719.tableM] at hb hm
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
