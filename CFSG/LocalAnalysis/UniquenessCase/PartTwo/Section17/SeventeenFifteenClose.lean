module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenParaTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenPDichotomy
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSixFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SevenLocal17Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSwapStep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenThreeConjOrbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSwapInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem gap17_15_threeConj_holds (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q)
    (h82 : F08.R82 D) (h17_1 : R17_1At D V₀ V hC.hyp125)
    (h17_7 : R17_7At D V₀ V L r q hC) (h17_11 : R17_11At D V₀ V L r q hC)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h127 : R127 D) (h117 : C117 D V₀ V)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h111 : W3Thm111 G) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h915 : W3Lem915 G) (hG15O : Gap17_15_TOrbitFour D V₀ V)
    (hP : Gap17_15_P D V₀ V L r q hC)
    (hAut : Gap17_15_autPGL2 D V₀ V L r q hC)
    (hInFSq : Gap17_15_threeConjInFSq D V₀ V L r q hC) :
    Gap17_15_threeConj D V₀ V L r q hC := by
  intro h7 hYs hgt
  obtain ⟨x, hxM, y, hyM, hxL, hyL, hyx⟩ := exists_three_conj_of_two_lt_ncard hgt
  exact gap17_15_threeConj_of_orbit D hC h82 h17_1 h17_7 h17_11 h1669 h127 h117 hTim hcat h66
    h86 h88 h126
    (s16c1614_sp_three_of_k_eq_one D
      (k_eq_one_of_three_conj D h82 hC.memL h7 hxM hyM hxL hyL hyx))
    hx h61 h111 h1114 h162 hTor h1482 h183 h915 hG15O hP hAut hInFSq h7 hYs hgt


theorem seventeen_fifteen_close (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h17_1 : R17_1At D V₀ V hC.hyp125) (h17_3 : R17_3At D V₀ V)
    (h17_7 : R17_7At D V₀ V L r q hC) (h17_10 : R17_10At D V₀ V L r q hC)
    (h17_11 : R17_11At D V₀ V L r q hC)
    (h17_13 : R17_13At D (fundPred q) V₀ V L r q hC)
    (h82 : F08.R82 D) (h847 : UC22.R847ThinNe3 D)
    (h880 : F08.R880 D) (h8107 : F08.R8107 D)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D)
    (h1114 : R1114 D) (h119 : F11.R119 D) (h117 : C117 D V₀ V)
    (h126 : R126 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h1217 : R1217 D)
    (hR1513 : R15_13Small D) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (hSg : UC6S846.SigmaStd D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h111 : W3Thm111 G)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h915 : W3Lem915 G) (hG15O : Gap17_15_TOrbitFour D V₀ V)
    (h43c : W3Lem45_2Chief) (h410 : W4Lem4_10) (h416 : Inputs1719.W4Lem4_16)
    (hW141 : Inputs1719.W4Thm14_1Used)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G) :
    R17_15At D (fundPred q) V₀ V L r q hC := by
  have hK : K_LieModelNotL2 := Inputs1719.k_LieModelNotL2_holds
  have hAut : Gap17_15_autPGL2 D V₀ V L r q hC := gap17_15_autPGL2_of D hC
  have hPairPGL : Gap17_15_pairPGL2 D V₀ V L r q hC := gap17_15_pairPGL2_of h410 D hC
  have hSplit : Gap17_15_swapSplit D V₀ V L r q hC := gap17_15_swapSplit_of D hC
  have hSwPair : Gap17_15_swapPairInner D V₀ V L r q hC :=
    gap17_15_swapPairInner_of D hC k_L27Local_holds
  have hP : Gap17_15_P D V₀ V L r q hC := gap17_15_P_of D hC k_L27Local_holds
  have hPGLInFSq : Gap17_15_threeConjInFSq D V₀ V L r q hC :=
    gap17_15_threeConjInFSq_holds h410 h43c D hC
  have h3 : Gap17_15_threeConj D V₀ V L r q hC :=
    gap17_15_threeConj_holds D hC h82 h17_1 h17_7 h17_11 h1669 h127 h117 hTim hcat h66 h86 h88 h126
      hx h61 h111 h1114 h162 hTor h1482 h183 h915 hG15O hP hAut hPGLInFSq
  have hSwInFSq : Gap17_15_swapInFSq D V₀ V L r q hC :=
    gap17_15_swapInFSq_of D hC h3
      (gap17_15_swapStep1_holds k_L27PermutesS3_holds D hC)
  have hOuterPara : Gap17_15_paraTwoOuter D V₀ V L r q hC :=
    gap17_15_paraTwoOuter_holds hTim hcat D h66 h86 h88 h126 hC h17_3 h17_7 h915 h3 hAut
  have hparaTwo : Gap17_15_paraTwo D V₀ V L r q hC :=
    gap17_15_paraTwo_holds hTim hcat D h66 h86 h88 h126 h93 k_L27Local_holds hC h17_3 h17_7
      hOuterPara
  have hOuterPair : Gap17_15_pairOuter D V₀ V L r q hC :=
    gap17_15_pairOuter_of D V₀ V L r q hC h17_7 hAut hPGLInFSq hSplit hSwPair hSwInFSq
      hPairPGL
  have hpair : Gap17_15_pair D V₀ V L r q hC :=
    gap17_15_pair_of_inputs D V₀ V L r q hC h17_7 k_L27Local_holds hOuterPair
  have hparaSix : Gap17_15_paraSix D V₀ V L r q hC :=
    gap17_15_paraSix_of_inputs D V₀ V L r q hC h1217 h127 h117 h17_7.1 hSg hR1513 hx
      h61 h126 h111 h1214 h82 h880 h847 h8107 h920 h119 hW141
      (b17_15BoundK2_holds h410 h43c (Inputs1719.w4Lem4_16b_of_w4Lem4_16 h416) D h82 hC) hpair
  have h17_14 := seventeen_fourteen D _ V₀ V L r q hC h127 h117 h17_7 h17_10 h17_11 h17_13 hK
  by_contra hnot
  have h14 := h17_14
  rcases h14 with hgt | ⟨-, hL2⟩ | h7
  · exact absurd hgt hnot
  · by_cases h7 : IsL2Over17 (Bar2 L) 7
    · exact seventeen_fifteen_of_seven D V₀ V L r q hC h1669 h17_7 h17_11 h127 h117 h111
        hx h61 h66 h1114 h162 hTor h1482 h183 h126 hparaTwo hpair hparaSix h7
    · exact seventeen_fifteen_of_not_seven D V₀ V L r q hC h17_7 h17_10 h17_11 h17_13
        h17_14 h127 h117 h111 hK hx h61 h66 h1114 h162 hTor h1482 h183 h126 h7 hnot
  · exact seventeen_fifteen_of_seven D V₀ V L r q hC h1669 h17_7 h17_11 h127 h117 h111
      hx h61 h66 h1114 h162 hTor h1482 h183 h126 hparaTwo hpair hparaSix h7
