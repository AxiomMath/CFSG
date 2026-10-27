module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComposeEarly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComposeSporadic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComposeUnitary
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComposeLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComposeFinal
public import CFSG.RankThree.GF2n.AssemblyFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22th
public import CFSG.RankThree.PartTwo.Sec11.Item116R2K1
public import CFSG.LocalAnalysis.UniquenessCase.UCK35wHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6R640Cert
public import CFSG.CGT.PushingUpLit.TwoKHolds
public import CFSG.LocalAnalysis.WeakClosure81.W19HoldsC
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846k
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankTwistedE6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeCentralCoverHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


structure Rows17 (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop where
  r1 : R17_1At D V₀ V hV
  r2 : R17_2At D V₀ V hV
  r33_3 : R17_33_3At D V₀ V
  r42 : R17_42At D V₀ V
  r57 : R17_57At D V₀ V
  r64_1 : R17_64_1At D V₀ V
  r64_2 : R17_64_2At D V₀ V
  r64_3 : R17_64_3At D V₀ V
  r65 : R17_65At D V₀ V
  r66_1 : R17_66_1At D V₀ V
  r67 : R17_67At D V₀ V
  r68 : R17_68At D V₀ V

structure Rows17Core (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop where
  r1 : R17_1At D V₀ V hV
  r2 : R17_2At D V₀ V hV
  r3 : R17_3At D V₀ V
  r33_3 : R17_33_3At D V₀ V
  r42 : R17_42At D V₀ V
  r57 : R17_57At D V₀ V
  r64_1 : R17_64_1At D V₀ V
  r64_2 : R17_64_2At D V₀ V
  r64_3 : R17_64_3At D V₀ V
  r65 : R17_65At D V₀ V
  r67 : R17_67At D V₀ V
  r68 : R17_68At D V₀ V

theorem compose17_rows_core
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h66 : UC6.R6_6 D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hSg : UC6S846.SigmaStd D) (h126 : R126 D) (h127 : R127 D) (h1114 : R1114 D)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h13s : SigmaRankThree13 D) (h8107 : F08.R8107 D)
    (h1214 : F12.R1214 D) (h69 : UC6.R6_9 D) (h899 : F08.R899 D)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h1219 : D.sig = D.sig1) (hR77 : F07.R77Eq D)
    (h78 : Inputs1719.PartOne.R7_8At5 D) (h76 : F07.R76 D) (h847 : R847Sec17 D) (h82 : F08.R82 D)
    (h880 : F08.R880 D) (h869 : F08.R869 D)
    (h920o : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D)
    (h920J1 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1 D)
    (h119 : F11.R119 D) (h1513 : R15_13Small D) (h891 : F08.R891 D) (h614 : UC6.R6_14 D)
    (h109 : Inputs1719.UC2_10_9 D) (h146 : UC2_14_6 D) (h898 : F08.R898 D)
    (h8108 : Inputs1719.PartOne.R8_108 D)
    (h8100 : CFSG.Open.evenRank G ≠ 3 → F08.R8100R D)
    (hE3 : CFSG.Open.evenRank G = 3 → F07.R77E2 D ∧ UC22.R847E3ThinNN D)
    (h147 : Inputs1719.UC2_14_7Three D)
    (h8103 : F08.R8103 D) (h136 : R136a D) (h148 : Inputs1719.R14_8 D) (h162 : W3Thm162Ext G)
    (h183 : W3Thm183 G) (h861 : W3Lem86_1 G) (h88 : W3Thm88 G) (h914N : W3Lem914N G)
    (h618 : W3_6_18 G) (h915 : W3Lem915 G) (h162g : W3Thm162Gt2 G)
    (h161 : CFSG.LocalAnalysis.WeakClosure81.W16One G)
    (h93s : CFSG.LocalAnalysis.WeakClosure81.Thm93Syl V₀ D.T) (h77 : Inputs1719.W4Lem7_7)
    (h106w : Inputs1719.W4Lem10_6Q) (h410 : Inputs1719.W4Lem4_10) (h43c : W3Lem45_2Chief)
    (h416 : Inputs1719.W4Lem4_16)
    (h5_11 : CFSG.LocalAnalysis.WeakClosure81.Asch5_11AS)
    (h5_13 : CFSG.LocalAnalysis.WeakClosure81.Asch5_13AS)
    (h411 : Inputs1719.W4Lem4_11Prime) (hFC3 : Inputs1719.K_FunCommuteThree) (h128 : W4Lem12_8)
    (h105w : Inputs1719.W4Lem10_5Q) (hKFun : Inputs1719.K_FunCommute)
    (hW141 : Inputs1719.W4Thm14_1Used)
    (hrowONan : Inputs1719.W4Thm11_1Row .ONan) (hrowJ2 : Inputs1719.W4Thm11_1Row .J2)
    (hrowHe : Inputs1719.W4Thm11_1RowM .He) (hrowHS : Inputs1719.W4Thm11_1RowM .HS)
    (hrowM22 : Inputs1719.W4Thm11_1RowA .M22)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hKONL : Inputs1719.K_ONanLattice) (h119w : Inputs1719.W4Lem11_9)
    (h115w : WeakClosure81.W4Lem11_5Twelve) (hFF : W4Thm12McClurg)
    (hKHe : Inputs1719.K_HeOuterParabolics)
    (h118w : Inputs1719.W4Lem11_8Rk)
    (hMc2F4 : W4McClurg2F4) (hMcTits : W4McClurgTits)
    (h3D4 : Inputs1719.W4Lem4_17TrialityD4N)
    (hMc3D4 : W4McClurg3D4) (h36 : Inputs1719.W4Lem3_6)
    (h146a : Inputs1719.W4Lem14_6aSmall) (hW142 : Inputs1719.W4Thm14_2Used)
    (hW143 : Inputs1719.W4Thm14_3)
    (hG8 : Gap17_8_graphOuterThree D V₀ V)
    (hG45U : Gap17_45_UniqueMaxFive D V₀ V)
    (hG5P : Gap17_5_A6Pair D V₀ V) (hG15O : Gap17_15_TOrbitFour D V₀ V) :
    Rows17Core D V₀ V hV := by
  have h111 : W3Thm111 G :=
    CFSG.LocalAnalysis.WeakClosure81.w3Thm111_unconditional
  have hTim : CFSG.CGT.Timmesfeld75.NodeStatement :=
    CFSG.RankThree.GF2n.nodeStatement_proved
  have hTor : W3Lem148Torus G :=
    CFSG.LocalAnalysis.WeakClosure81.w3Lem148Torus_holds
  have h1482 : W3Lem148_2 G :=
    CFSG.LocalAnalysis.WeakClosure81.w3Lem148_2_holds
  have hThin : ThinList13 :=
    thinList13_holds
  have hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian :=
    CFSG.RankThree.PartTwo.Sec11.cyclicSylowThreeOutAbelian_holds
  have hK35 : UCK.K35w :=
    UCK.k35w_holds
  have hKLie : K_LieModelNotL2 :=
    Inputs1719.k_LieModelNotL2_holds
  have hKU3 : Inputs1719.K_U3FourPowThreeRankOne :=
    Inputs1719.k_U3FourPowThreeRankOne_holds
  have hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hKHJ : K_HJData :=
    Inputs1719.k_HJData_holds
  have hgr : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hU3Syl : UCK.U3Syl :=
    UCK.u3Syl_of_griess hgr
  have hU3Cen : UCK.U3Center :=
    UCK.u3Center_of_griess hgr
  have h6402 : UC6.R6_40_2 D :=
    UC6.r6_40_2_holds CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
      CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds D
  have h117 : C117 D V₀ V :=
    ElevenNine.c117_of_hyp11 D h869 (Hyp125.hyp11 h127 hV)
  have h1217 : R1217 D :=
    r1217_of_twelve_seventeen D hx h61 h127 h1214
  have h1211 : R1211_1 D :=
    r1211_1_of_twelve_eleven D hx h61 h63 h66 h127 h1114 h183
      (CFSG.LocalAnalysis.WeakClosure81.w3Thm193_of_w3Thm162 h162g)
  have hN : uc22p20rNativeGriess :=
    UC22.uc22p20r_nativeGriess
  have h115 : F11.R115 D :=
    UC22.uc22p22q_r115_of D hx h61
  have h127One : R127One D :=
    fun h124 _ hV hTI h8 => twelve_seven_one hTim hcat D h861 h126 h124 hV hTI h8
  have h846 : F08.R846 D :=
    UC6S846.r846_of_rank_three hgr D hSg (F07.R76Sig_of_R76 D h76) h614
  have hKCR : Inputs1719.K_CartanRank :=
    Inputs1719.k_CartanRank_of_griess_of_twistedE6 hN
      (Inputs1719.k_CartanRank_twistedE6_of_griess hN)
  have hKBT : Inputs1719.K_BorelTorusAbelian :=
    Inputs1719.k_BorelTorusAbelian_holds
  have hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds
  have hKBT2 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34 :=
    Inputs1719.k_BorelTorusAbelianRankTwoNotL34_of_griess hN
  have hKCR3 : Inputs1719.K_CartanRankLeThree :=
    Inputs1719.k_CartanRankLeThree_of_griess hN
  have hLieOdd : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev :=
    UC22.uc22p20x_lieOddRankChev hgr
  have hKG : CFSG.Open.IsKGroup ↥D.M :=
    D.standing.kProper.isKGroup D.M (UC22.uc22br4_M_ne_top D)
  have h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T := by
    by_cases h0 : V₀ = ⊥
    · subst h0
      intro h9
      have h2 := h9.rk_gt
      rw [CFSG.Quasithin.rk_bot] at h2
      omega
    · exact thm93_of_thm93Syl D (hyp125_inCalV hV h0) h93s
  obtain ⟨r1, r2, r3, r5, r6⟩ :=
    compose17_early D V₀ V hV h63 h126 h127 h1211 h111 h1669 hSg h1219 hR77 hx h61 h1214 h115 h78
      h76 h72 h847.1 h82 h880 h66 h1114 h162 hTor h1482 h183 h869 h117 h77 h106w hTim hcat h861 h88
      h914N h410 h43c h618 h93 h416 hO hThin hKLie h8107 hKU3 h920o h5_11 h5_13 hG8 h411
      hFC3 h128 h105w hKFun h119 h1217 h1513 h915 hW141 hG5P hG15O
  have r17 : R17_17At D V₀ V :=
    compose17_sporadic D V₀ V hV r1 hx h61 h127 h162 h126 h117 h869 h1214 h128 h77 hrowONan
      hrowJ2 hrowHe hrowHS hrowM22 h82 h880
      hKS1 hKONL hSg h1114 hTor h1482 h111 h8107 h920J1 h43c h63 h119w h115w h6402
      hFF h127One hTim hcat h66 h88 h93 h618 h861 h183 h1669 h416 hKHe h118w h5_11 h5_13
      h162g hKHJ h1219
  obtain ⟨r31, r32, r33_2, r33_3⟩ :=
    compose17_unitary D V₀ V hV r1 hx h61 h126 h111 h127 h1114 h162 hTor h1482 h869 h6402 hFF
      hMc2F4 hMcTits h3D4 hKCR hSg hMc3D4 h891 h76 h614 h72 hK35 h13s h109 h117 hU3Syl h43c h416
      hU3Cen h1214 h128 h36 h82 h846 h847.2 h1219 h146 h66 h183 h898 h162g h161
  have r42 : R17_42At D V₀ V :=
    compose17_lie D V₀ V hV r1 r5 r6 r17 r31 r32 r33_2 r33_3 h82 h880 hN hSg hKBT h13s h8108 hKCR
      Inputs1719.k_ThreeCentralRankTwo_holds h899 h8100 hE3 hKBT2 hKCR3 h846 h76 h614 h1219 hKG hKF
      h93 h147 hG45U h1669 hTim hcat h66 h88
      h126 h861 h111 h61 hx h127 h1114 h162 hTor h1482 h183 h1214 h869 h6402 hFF h146a h638 hLieOdd
      hW142 h8103 h72 hK35
  obtain ⟨r57, r64_1, r64_2, r64_3, r65, r67, r68⟩ :=
    compose17_final D V₀ V hV r1 r2 r3 r6 r17 r33_2 r42 h109 h127 hx h61 h126 h111 hW143 hSg hThin
      hCyc h638 h76 h63 h614 hK35 h72 h8100 h13s h869 h69 h1219 h1669 h136 h8107 h148 h82
  exact ⟨r1, r2, r3, r33_3, r42, r57, r64_1, r64_2, r64_3, r65, r67, r68⟩

theorem rows136_at
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h66 : UC6.R6_6 D)
    (h72 : F07.R72 D) (hSg : UC6S846.SigmaStd D) (h126 : R126 D) (h127 : R127 D)
    (h1114 : R1114 D) (h13s : SigmaRankThree13 D) (h1214 : F12.R1214 D)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h1219 : D.sig = D.sig1)
    (hR77 : F07.R77Eq D) (h78 : Inputs1719.PartOne.R7_8At5 D) (h76 : F07.R76 D)
    (h847 : R847Sec17 D) (h82 : F08.R82 D) (h869 : F08.R869 D)
    (h891 : F08.R891 D) (h614 : UC6.R6_14 D) (h109 : Inputs1719.UC2_10_9 D)
    (h146 : UC2_14_6 D) (h898 : F08.R898 D) (h162 : W3Thm162Ext G) (h183 : W3Thm183 G)
    (h162g : W3Thm162Gt2 G) (h161 : CFSG.LocalAnalysis.WeakClosure81.W16One G)
    (h43c : W3Lem45_2Chief) (h416 : Inputs1719.W4Lem4_16) (h128 : W4Lem12_8)
    (hFF : W4Thm12McClurg) (hMc2F4 : W4McClurg2F4) (hMcTits : W4McClurgTits)
    (h3D4 : Inputs1719.W4Lem4_17TrialityD4N) (hMc3D4 : W4McClurg3D4)
    (h36 : Inputs1719.W4Lem3_6) :
    R17_1At D V₀ V hV ∧ R17_2_2At D V₀ V hV ∧ R17_2_3At D V₀ V hV ∧
      R17_3At D V₀ V ∧ R17_33_2At D V₀ V ∧ R17_33_3At D V₀ V := by
  have h111 : W3Thm111 G :=
    CFSG.LocalAnalysis.WeakClosure81.w3Thm111_unconditional
  have hTor : W3Lem148Torus G :=
    CFSG.LocalAnalysis.WeakClosure81.w3Lem148Torus_holds
  have h1482 : W3Lem148_2 G :=
    CFSG.LocalAnalysis.WeakClosure81.w3Lem148_2_holds
  have hK35 : UCK.K35w :=
    UCK.k35w_holds
  have hgr : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hU3Syl : UCK.U3Syl :=
    UCK.u3Syl_of_griess hgr
  have hU3Cen : UCK.U3Center :=
    UCK.u3Center_of_griess hgr
  have h6402 : UC6.R6_40_2 D :=
    UC6.r6_40_2_holds CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
      CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds D
  have h117 : C117 D V₀ V :=
    ElevenNine.c117_of_hyp11 D h869 (Hyp125.hyp11 h127 hV)
  have h1211 : R1211_1 D :=
    r1211_1_of_twelve_eleven D hx h61 h63 h66 h127 h1114 h183
      (CFSG.LocalAnalysis.WeakClosure81.w3Thm193_of_w3Thm162 h162g)
  have hN : uc22p20rNativeGriess :=
    UC22.uc22p20r_nativeGriess
  have h115 : F11.R115 D :=
    UC22.uc22p22q_r115_of D hx h61
  have h846 : F08.R846 D :=
    UC6S846.r846_of_rank_three hgr D hSg (F07.R76Sig_of_R76 D h76) h614
  have hKCR : Inputs1719.K_CartanRank :=
    Inputs1719.k_CartanRank_of_griess_of_twistedE6 hN
      (Inputs1719.k_CartanRank_twistedE6_of_griess hN)
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
    seventeen_three D V₀ V hV hx h847.1 r2
  obtain ⟨-, -, r33_2, r33_3⟩ :=
    compose17_unitary D V₀ V hV r1 hx h61 h126 h111 h127 h1114 h162 hTor h1482 h869 h6402 hFF
      hMc2F4 hMcTits h3D4 hKCR hSg hMc3D4 h891 h76 h614 h72 hK35 h13s h109 h117 hU3Syl h43c h416
      hU3Cen h1214 h128 h36 h82 h846 h847.2 h1219 h146 h66 h183 h898 h162g h161
  exact ⟨r1, r2_2, r2_3, r3, r33_2, r33_3⟩

theorem compose17_rows
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h66 : UC6.R6_6 D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hSg : UC6S846.SigmaStd D) (h126 : R126 D) (h127 : R127 D) (h1114 : R1114 D)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h13s : SigmaRankThree13 D) (h8107 : F08.R8107 D)
    (h1214 : F12.R1214 D) (h69 : UC6.R6_9 D) (h899 : F08.R899 D)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h1219 : D.sig = D.sig1) (hR77 : F07.R77Eq D)
    (h78 : Inputs1719.PartOne.R7_8At5 D) (h76 : F07.R76 D) (h847 : R847Sec17 D) (h82 : F08.R82 D)
    (h880 : F08.R880 D) (h869 : F08.R869 D)
    (h920o : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D)
    (h920J1 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1 D) (h920e : R920L2E D)
    (h119 : F11.R119 D) (h1513 : R15_13Small D) (h891 : F08.R891 D) (h614 : UC6.R6_14 D)
    (h109 : Inputs1719.UC2_10_9 D) (h146 : UC2_14_6 D) (h898 : F08.R898 D)
    (h8108 : Inputs1719.PartOne.R8_108 D)
    (h8100 : CFSG.Open.evenRank G ≠ 3 → F08.R8100R D)
    (hE3 : CFSG.Open.evenRank G = 3 → F07.R77E2 D ∧ UC22.R847E3ThinNN D)
    (h147 : Inputs1719.UC2_14_7Three D)
    (h8103 : F08.R8103 D) (h136 : R136a D) (h148 : Inputs1719.R14_8 D) (h162 : W3Thm162Ext G)
    (h183 : W3Thm183 G) (h861 : W3Lem86_1 G) (h88 : W3Thm88 G) (h914N : W3Lem914N G)
    (h618 : W3_6_18 G) (h915 : W3Lem915 G) (h162g : W3Thm162Gt2 G)
    (h161 : CFSG.LocalAnalysis.WeakClosure81.W16One G)
    (h93s : CFSG.LocalAnalysis.WeakClosure81.Thm93Syl V₀ D.T) (h77 : Inputs1719.W4Lem7_7)
    (h106w : Inputs1719.W4Lem10_6Q) (h410 : Inputs1719.W4Lem4_10) (h43c : W3Lem45_2Chief)
    (h416 : Inputs1719.W4Lem4_16)
    (h5_11 : CFSG.LocalAnalysis.WeakClosure81.Asch5_11AS)
    (h5_13 : CFSG.LocalAnalysis.WeakClosure81.Asch5_13AS)
    (h411 : Inputs1719.W4Lem4_11Prime) (hFC3 : Inputs1719.K_FunCommuteThree) (h128 : W4Lem12_8)
    (h105w : Inputs1719.W4Lem10_5Q) (hKFun : Inputs1719.K_FunCommute)
    (hW141 : Inputs1719.W4Thm14_1Used)
    (hrowONan : Inputs1719.W4Thm11_1Row .ONan) (hrowJ2 : Inputs1719.W4Thm11_1Row .J2)
    (hrowHe : Inputs1719.W4Thm11_1RowM .He) (hrowHS : Inputs1719.W4Thm11_1RowM .HS)
    (hrowM22 : Inputs1719.W4Thm11_1RowA .M22)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hKONL : Inputs1719.K_ONanLattice) (h119w : Inputs1719.W4Lem11_9)
    (h115w : WeakClosure81.W4Lem11_5Twelve) (hFF : W4Thm12McClurg)
    (hKHe : Inputs1719.K_HeOuterParabolics)
    (h118w : Inputs1719.W4Lem11_8Rk)
    (hMc2F4 : W4McClurg2F4) (hMcTits : W4McClurgTits)
    (h3D4 : Inputs1719.W4Lem4_17TrialityD4N)
    (hMc3D4 : W4McClurg3D4) (h36 : Inputs1719.W4Lem3_6)
    (h146a : Inputs1719.W4Lem14_6aSmall) (hW142 : Inputs1719.W4Thm14_2Used)
    (hW143 : Inputs1719.W4Thm14_3)
    (hG8 : Gap17_8_graphOuterThree D V₀ V)
    (hG45U : Gap17_45_UniqueMaxFive D V₀ V)
    (hG5P : Gap17_5_A6Pair D V₀ V) (hG15O : Gap17_15_TOrbitFour D V₀ V) :
    Rows17 D V₀ V hV := by
  have hc := compose17_rows_core D V₀ V hV hx h61 h63 h66 h638 h72 hSg h126 h127 h1114 hcat h13s
    h8107 h1214 h69 h899 h1669 h1219 hR77 h78 h76 h847 h82 h880 h869 h920o h920J1
    h119 h1513 h891 h614 h109 h146 h898 h8108 h8100 hE3 h147 h8103 h136 h148 h162 h183
    h861 h88 h914N
    h618 h915 h162g h161 h93s h77 h106w h410 h43c h416 h5_11 h5_13 h411 hFC3 h128 h105w hKFun
    hW141 hrowONan hrowJ2 hrowHe hrowHS hrowM22 hKS1 hKONL h119w h115w hFF hKHe h118w hMc2F4
    hMcTits h3D4 hMc3D4 h36 h146a hW142 hW143 hG8 hG45U hG5P hG15O
  exact ⟨hc.r1, hc.r2, hc.r33_3, hc.r42, hc.r57, hc.r64_1, hc.r64_2, hc.r64_3, hc.r65,
    seventeen_sixtysix_one D h869 hc.r3 h8107 h920e h148 hc.r42 hc.r64_1
      hc.r64_2 hc.r64_3,
    hc.r67, hc.r68⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
