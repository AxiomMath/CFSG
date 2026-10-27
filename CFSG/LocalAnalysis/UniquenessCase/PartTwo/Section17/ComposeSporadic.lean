module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenAS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineteenDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwenty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22Close
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyThreeBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFourBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAConfigFalse
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixBOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowJ1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem compose17_sporadic
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) (r1 : R17_1At D V₀ V hV) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h162 : W3Thm162Ext G) (h126 : R126 D) (h117 : C117 D V₀ V)
    (h869 : F08.R869 D) (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h77 : Inputs1719.W4Lem7_7)
    (hrowONan : Inputs1719.W4Thm11_1Row .ONan) (hrowJ2 : Inputs1719.W4Thm11_1Row .J2)
    (hrowHe : Inputs1719.W4Thm11_1RowM .He) (hrowHS : Inputs1719.W4Thm11_1RowM .HS)
    (hrowM22 : Inputs1719.W4Thm11_1RowA .M22) (h82 : F08.R82 D) (h880 : F08.R880 D)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hKONL : Inputs1719.K_ONanLattice) (hSg : UC6S846.SigmaStd D) (h1114 : R1114 D)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h111 : W3Thm111 G) (h8107 : F08.R8107 D)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1 D)
    (h43c : W3Lem45_2Chief) (h63 : UC6.R6_3 D) (h119w : Inputs1719.W4Lem11_9)
    (h115w : WeakClosure81.W4Lem11_5Twelve) (h6402 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (h127One : R127One D) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h618 : W3_6_18 G) (h861 : W3Lem86_1 G)
    (h183 : W3Thm183 G) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h416 : Inputs1719.W4Lem4_16)
    (hKHe : Inputs1719.K_HeOuterParabolics) (h118w : Inputs1719.W4Lem11_8Rk)
    (h5_11 : CFSG.LocalAnalysis.WeakClosure81.Asch5_11AS)
    (h5_13 : CFSG.LocalAnalysis.WeakClosure81.Asch5_13AS) (h162g : W3Thm162Gt2 G) (hKHJ : K_HJData)
    (h1219 : D.sig = D.sig1) :
    R17_17At D V₀ V := by
  have r18 : R17_18At D V₀ V :=
    seventeen_eighteen_holds D V₀ V (fun _ => r1) hx h61 h127 h162 h126 h117 h869 h1214 h128 h77
      hrowONan h82 h880
      hKS1 hKONL hSg
  have r19 : R17_19At D V₀ V :=
    seventeen_nineteen_of D V₀ V hx h61 h127 h1114 h162 hTor h1482 h126 h111 h117 h8107 h920 h1214
      h128 h77 Inputs1719.w4Thm11_1Row_J1_holds h43c
  have r20 : R17_20At D V₀ V :=
    seventeen_twenty D V₀ V r18 r19
  have r21 : R17_21At D V₀ V :=
    seventeen_twentyone_of_M22K D V₀ V hV r1 r20 h869 h117 hx h61 h63 h127 h1114 h162 hTor h1482
      h126 h111 h128 h119w hrowM22 hrowHS h115w h6402 hFF h1214 h127One hTim hcat h66 h88 h93
      h618 h861 h183 h1669 h416 h77
  have r22 : R17_22At D V₀ V :=
    seventeen_twentytwo D V₀ V hV r20 r21 h880
  have r23 : R17_23At D V₀ V :=
    seventeen_twentythree_holds D V₀ V hV r20 r21 r22 h869 h127 h6402 hFF hx h61 h1114 h162 hTor
      h1482 h126 h111 h1214 h128 h416 hrowHe hKHe
  have r24 : R17_24At D V₀ V :=
    seventeen_twentyfour_holds D V₀ V hV r20 r23 hx h61 h127 h1214 h128 h869 h117 h6402 hFF h77
      hrowJ2 h118w
  have r25 : R17_25At D V₀ V :=
    seventeen_twentyfive_of_inputs D V₀ V r24 r20 r22 r23 hSg h880 h869 h127 h117 hx h61 h1114
      h162 hTor h1482 h126 h111
  have r26a : R17_26aAt D V₀ V :=
    seventeen_twentysix_a_of_KF hTim hcat r20 r22 r23 r25 hSg h880 h61 h66 h88 h861
      (fun _ _ => h93) h5_11 h5_13 h117
  have r26b_1 : R17_26b_1At D V₀ V :=
    seventeen_twentysix_b_one D V₀ V hx h880 r22 r23 r25 r26a
  have r26b_2 : R17_26b_2At D V₀ V :=
    seventeen_twentysix_b_two D V₀ V hx r22 r23 r25 r26a
  have r26b_3 : R17_26b_3At D V₀ V :=
    seventeen_twentysix_b_three D V₀ V hV r25 hx h61 h127 h1114 h162g h111
  have r27 : R17_27At D V₀ V :=
    seventeen_twentyseven D V₀ V r25 r26a r26b_1 r26b_3 r22 r23 hSg h61
  have r28 : R17_28At D V₀ V :=
    seventeen_twentyeight D V₀ V hV r24 r27 hx h61 h66 h126 h127 h1114 h111 h183
  have r29_1 : R17_29_1At D V₀ V :=
    seventeen_twentynine_one D V₀ V r22 r23 r25 r26b_2 h61
  have r29_2 : R17_29_2At D V₀ V :=
    seventeen_twentynine_two D V₀ V r22 r23 r25
  have r29_3 : R17_29_3At D V₀ V :=
    seventeen_twentynine_three D V₀ V r22 r23 r25
  have r30 : R17_30At D V₀ V :=
    seventeen_thirty D V₀ V hKHJ r20 r23 r25 r29_1 r29_2
  have r17 : R17_17At D V₀ V :=
    seventeen_seventeen D V₀ V hV r22 r23 r25 r26b_1 r27 r28 r29_1 r29_3 r30 hSg h1219
  exact r17

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
