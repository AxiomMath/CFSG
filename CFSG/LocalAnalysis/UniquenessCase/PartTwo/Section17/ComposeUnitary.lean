module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsTwoF4NormalHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOneFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFourHoldsBot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveCaseTwoGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyPStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyThreeFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveNTwoV0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem compose17_unitary
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) (r1 : R17_1At D V₀ V hV) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h869 : F08.R869 D)
    (h6402 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg) (hMc2F4 : W4McClurg2F4) (hMcTits : W4McClurgTits)
    (h3D4 : Inputs1719.W4Lem4_17TrialityD4N) (hKCR : Inputs1719.K_CartanRank)
    (hSg : UC6S846.SigmaStd D)
    (hMc3D4 : W4McClurg3D4) (h891 : F08.R891 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (h72 : F07.R72 D) (hK35 : UCK.K35w) (h13s : SigmaRankThree13 D) (h109 : Inputs1719.UC2_10_9 D)
    (h117 : C117 D V₀ V) (hU3Syl : UCK.U3Syl) (h43c : W3Lem45_2Chief) (h416 : Inputs1719.W4Lem4_16)
    (hU3Cen : UCK.U3Center) (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h36 : Inputs1719.W4Lem3_6)
    (h82 : F08.R82 D) (h846 : F08.R846 D) (h847 : R847SU3G4 D)
    (h1219 : D.sig = D.sig1) (h146 : UC2_14_6 D) (h66 : UC6.R6_6 D) (h183 : W3Thm183 G)
    (h898 : F08.R898 D) (h162g : W3Thm162Gt2 G) (h161 : CFSG.LocalAnalysis.WeakClosure81.W16One G) :
    R17_31At D V₀ V ∧ R17_32At D V₀ V ∧ R17_33_2At D V₀ V ∧ R17_33_3At D V₀ V := by
  have h2F4 : Inputs1719.W4Lem4_17TwoF4N := Inputs1719.w4Lem4_17TwoF4N_holds h43c
  have r31 : R17_31At D V₀ V :=
    seventeen_thirtyone D hx h61 h126 h111 h127 h1114 h162 hTor h1482 h869 h6402 hFF hMc2F4
      hMcTits h2F4 hKCR hSg V₀ V hV r1
  have r32 : R17_32At D V₀ V :=
    seventeen_thirtytwo_holds D V₀ V hV hx h61 h126 h111 h869 h127 h6402 hFF hMc3D4 r1 h891 hSg
      h76 h614 h72 hK35 h13s h109 h3D4
  have r34 : R17_34At D V₀ V :=
    seventeen_thirtyfour_holds_of_inputs D hx h61 h127 h1114 h162 hTor h1482 h126 h111 h869 h117
      hU3Syl h43c h416 h6402 hFF (fun _ => r1) hSg hU3Cen h1214 h128 h36 h82 h846 h76 h614
  have hG35' : Gap17_35_1_nTwo D V₀ V :=
    gap17_35_1_nTwo_of_V0 D V₀ V r34 hx h61 h66 h127 h1114 h1214 h128 h117 hU3Syl h162g h183
      h161 (fun h0 => seventeen_thirtysix_a_of_ne_bot D V₀ V h0 (fun _ => r1) hSg hU3Cen hU3Syl)
      (gap17_35_1_nTwoV0_holds D V₀ V)
  have r35 : R17_35At D V₀ V :=
    seventeen_thirtyfive_of_inputs D r34 hx h61 h127 h1214 h128 h869 h117 hU3Syl h36 hSg h82
      hU3Cen h846 h76 h614 hG35'
  have r36a : R17_36aAt D V₀ V :=
    seventeen_thirtysix_a_of_inputs D V₀ V r35 (fun _ => r1) hSg hU3Cen hU3Syl
  have r36b : R17_36bAt D V₀ V :=
    seventeen_thirtysix_b D r35 r34.1 r36a h847 h846 hx hSg h1219 h146 h61 h66 h127 h1114 h162 hTor
      h1482 h183
  have r37 : R17_37At D V₀ V :=
    seventeen_thirtyseven D r35 r36a r36b h898 h109 h869 hU3Syl
  have r38 : R17_38At D V₀ V :=
    seventeen_thirtyeight D V₀ V r37
  have r39 : R17_39At D V₀ V :=
    seventeen_thirtynine D hx h61 h66 h127 h1114 h162g h183 h161 r35 r36a r38
  have r40 : R17_40At D V₀ V :=
    seventeen_forty (fun _ => r1) r35 hSg hx h61 h127 h1214
  have r41_3 : R17_41_3At D V₀ V :=
    seventeen_fortyone_three D V₀ V r40 r35 hSg hx h61 h127 h1214
  have r33_2 : R17_33_2At D V₀ V :=
    seventeen_thirtythree_two D V₀ V hV r35 r39 r41_3 hx h61 h126 h127 h1214 h111
  have r33_3 : R17_33_3At D V₀ V :=
    seventeen_thirtythree_three D V₀ V hV r35 r39 r41_3 hx h61 h126 h127 h1214 h111
  exact ⟨r31, r32, r33_2, r33_3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
