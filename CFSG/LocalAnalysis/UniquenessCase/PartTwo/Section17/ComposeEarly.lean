module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwoB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwoFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwoFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6Close
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightGraphOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenStructureProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenClose
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixO2RestChar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G176ExcRankThreeHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U33AutE8Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33AutE8Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem compose17_early
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) (h63 : UC6.R6_3 D) (h126 : R126 D)
    (h127 : R127 D) (h1211 : R1211_1 D) (h111 : W3Thm111 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hR77 : F07.R77Eq D) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h1214 : F12.R1214 D) (h115 : F11.R115 D)
    (h78 : Inputs1719.PartOne.R7_8At5 D) (h76 : F07.R76 D)
    (h72 : F07.R72 D) (h847 : R847Thin17 D) (h82 : F08.R82 D) (h880 : F08.R880 D) (h66 : UC6.R6_6 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h869 : F08.R869 D) (h117 : C117 D V₀ V) (h77 : Inputs1719.W4Lem7_7)
    (h106w : Inputs1719.W4Lem10_6Q) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h861 : W3Lem86_1 G) (h88 : W3Thm88 G)
    (h914N : W3Lem914N G)
    (h410 : Inputs1719.W4Lem4_10) (h43c : W3Lem45_2Chief) (h618 : W3_6_18 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h416 : Inputs1719.W4Lem4_16)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) (hThin : ThinList13)
    (hKLie : K_LieModelNotL2) (h8107 : F08.R8107 D) (hKU3 : Inputs1719.K_U3FourPowThreeRankOne)
    (h920o : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D)
    (h5_11 : CFSG.LocalAnalysis.WeakClosure81.Asch5_11AS)
    (h5_13 : CFSG.LocalAnalysis.WeakClosure81.Asch5_13AS) (hG8 : Gap17_8_graphOuterThree D V₀ V)
    (h411 : Inputs1719.W4Lem4_11Prime)
    (hFC3 : Inputs1719.K_FunCommuteThree) (h128 : W4Lem12_8) (h105w : Inputs1719.W4Lem10_5Q)
    (hKFun : Inputs1719.K_FunCommute) (h119 : F11.R119 D) (h1217 : R1217 D)
    (h1513 : R15_13Small D) (h915 : W3Lem915 G) (hW141 : Inputs1719.W4Thm14_1Used)
    (hG5P : Gap17_5_A6Pair D V₀ V) (hG15O : Gap17_15_TOrbitFour D V₀ V) :
    R17_1At D V₀ V hV ∧ R17_2At D V₀ V hV ∧ R17_3At D V₀ V ∧ R17_5At D V₀ V ∧ R17_6At D V₀ V := by
  have hKexc : K_G176ExcRankThree := Inputs1719.k_G176ExcRankThree_holds
  have hKU33 : Inputs1719.K_U33AutE8 := Inputs1719.k_U33AutE8_holds
  have hKL33 : Inputs1719.K_L33AutE8 := Inputs1719.k_L33AutE8_holds
  have r1 : R17_1At D V₀ V hV :=
    seventeen_one D h63 h126 h127 h1211 h111 hV h1669
  have r2_1 : R17_2_1At D V₀ V :=
    seventeen_two_one D hSg h1219 hR77 hV
  have r2_2 : R17_2_2At D V₀ V hV :=
    seventeen_two_two D hSg h1219 hR77 hV r1
  have r2_3 : R17_2_3At D V₀ V hV :=
    seventeen_two_three D hSg h1219 hR77 h63 hx h61 h126 h127 h111 hV r1
  have r2_4 : R17_2_4At D V₀ V :=
    seventeen_two_four D hV r2_2 r2_3 hx h61 h127 h1214 h115
  have r2_5 : R17_2_5At D V₀ V :=
    seventeen_two_five D V₀ V hV r2_1 r2_2 r2_3 r2_4 r1 hSg h1219 h78 h76 h72 h63
  have r2 : R17_2At D V₀ V hV := ⟨r2_1, r2_2, r2_3, r2_4, r2_5⟩
  have r3 : R17_3At D V₀ V :=
    seventeen_three D V₀ V hV hx h847 r2
  have r5 : R17_5At D V₀ V :=
    seventeen_five_of_A6Inputs hV r1 h82 h880 hx h61 h66 h127 h1114 h162 hTor h1482 h183 h111 h126
      h869 h117 h1669 h77 h106w hTim hcat h861 h88 h914N h410 h43c h618 h93 h416 hG5P
  have h7 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_7At D V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_seven D V₀ V L r q hC hO hThin hKLie r3 h869 h8107 hKU3 h920o
  have h8 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_8At D V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_eight_of_three hC h880 r1 (h7 L r q hC).1 h127 h117 hKU33 hTim hcat h861 h88 h93
        h5_11 h5_13 hG8 h1669 h77 hKL33 h411 h869 hx h61 h66 h1114 h162 hTor h1482 h183 h111 h126
        h618 h416
  have h9 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_9At D V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_nine D V₀ V L r q hC r1 (h8 L r q hC) h82 hFC3
  have h10 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_10At D V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_ten D V₀ V L r q hx h61 h127 h1214 h128 h105w hC r5 (h9 L r q hC)
  have h11 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_11At D V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_eleven D V₀ V L r q hC (h9 L r q hC) h77 h106w
  have h13 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_13At D (fundPred q) V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_thirteen_of_kgroups D V₀ V L r q hC (h9 L r q hC) hKFun h43c h410 h411
  have h15 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_15At D (fundPred q) V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_fifteen_close D V₀ V L r q hC r1 r3 (h7 L r q hC) (h10 L r q hC) (h11 L r q hC)
        (h13 L r q hC) h82 (r847ThinNe3_of_r847Thin17 h847) h880 h8107 h920o h1114 h119 h117
        h126 h127 h1214 h1217 h1513 h1669
        hx h61 h66 hSg h861 h88 h93 h111 h162 hTor h1482 h183 h915 hG15O h43c h410 h416 hW141 hTim
        hcat
  have h16 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_16At D (fundPred q) V₀ V L r q hC :=
    fun L r q hC =>
      seventeen_sixteen D V₀ V L r q hC (h7 L r q hC) (h9 L r q hC) h61 h63 h76 hSg
  have r6 : R17_6At D V₀ V :=
    seventeen_six_of_steps_of_inputs_kfacts D V₀ V hV h7 h15 h16 hx h61 h126 h111 h127 h1114 h162
      hTor h1482 h117 h82 hSg hKexc h76
  exact ⟨r1, r2, r3, r5, r6⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
