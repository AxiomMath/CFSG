module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFourHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFourFixBot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixABot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34ThreeCentralizerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleAltTwoHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

section Certified


theorem gap17_34_bBoundVZeroTrivial_holds
    (D : Data G) {V₀ V : Subgroup G} (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h869 : F08.R869 D) (hSyl : UCK.U3Syl) (h45 : W3Lem45_2Chief)
    (h416 : Inputs1719.W4Lem4_16) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV) (hSg : SigmaStd D)
    (hCen : UCK.U3Center) (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h36 : W4Lem3_6)
    (h82 : F08.R82 D) (h846 : F08.R846 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D) :
    Gap17_34_bBoundVZeroTrivial D V₀ V := by
  intro hV0
  subst hV0
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  have hBorel : K_U3CartanRank := Inputs1719.k_U3CartanRank_holds
  have hK : K_SU3EightBorelNine := Inputs1719.k_SU3EightBorelNine_holds
  have hK9 : K_SU3EightTorusE9 := Inputs1719.k_SU3EightTorusE9_holds
  have hNat : K_SU3NaturalModule := Inputs1719.k_SU3NaturalModule_of_w4_holds h128 h36
  have hC : K_U34ThreeCentralizer := k_U34ThreeCentralizer_holds
  have hfix : ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D ⊥ V L n),
      fixV (barSub ⊥ V c.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ :=
    fun _ _ c => fixV_conjClosure_eq_bot_of_ctx17_33 D h869 h127 h640 hFF hSyl c
  exact hbBound_of_hbBoundA
    (hbBound_holds (Inputs1719.w4Lem4_16b_of_w4Lem4_16 h416)
      (k_U3Index_of_normal_and_F Inputs1719.k_U3IndexNormal_holds
        S17.k_U3IndexF_holds h45) D ⊥ V)
    (fun _ _ c => barSub_ne_bot_of_v0_bot D h869 h127 hSyl c.hyp125 c.mem_calC c.shape)
    (htr_of_R17_36aAt (seventeen_thirtysix_a_bot D h1 hSg hK3 hCen hSyl hBorel hK hK9 hx h61
      h127 h1214 h869 hNat h82 hC h846 h76 h614 hfix))
    hfix

theorem seventeen_thirtyfour_holds_of_inputs (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h869 : F08.R869 D) {V₀ V : Subgroup G} (h117 : C117 D V₀ V)
    (hSyl : UCK.U3Syl) (h45 : W3Lem45_2Chief)
    (h416 : Inputs1719.W4Lem4_16) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV) (hSg : SigmaStd D)
    (hCen : UCK.U3Center) (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h36 : W4Lem3_6)
    (h82 : F08.R82 D) (h846 : F08.R846 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D) :
    R17_34At D V₀ V :=
  seventeen_thirtyfour_holds D hx h61 h127 h1114 h162 hTor h1482 h126 h111 h869 h117 hSyl h45
    h416 h640 hFF h1 hSg hCen
    (gap17_34_bBoundVZeroTrivial_holds D hx h61 h127 h869 hSyl h45 h416 h640 hFF h1 hSg hCen
      h1214 h128 h36 h82 h846 h76 h614)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
