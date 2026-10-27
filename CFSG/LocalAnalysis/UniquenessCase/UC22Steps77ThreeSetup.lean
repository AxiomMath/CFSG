module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main79Three
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRestEHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R869Three
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S218XT
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2114R3LF
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2114R3LK2
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2114D4T
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2114K2T
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2251RStarSn
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwoThree
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2112aF2Even2
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2122F3SzQ5T
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HF
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CAssembly
public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps77ThreeS1617
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229S15C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R77E2Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DProof
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNTwo
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2122NoPairR
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4TThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218K
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PMain
public import CFSG.LocalAnalysis.UniquenessCase.UC22K108HCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215SetupThree
public import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07CardThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]

theorem steps77Three_dataOfSetup
    (hGF : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause)
    (hK : F10.K105SporRest) (hK332 : UCK.K332Cyc)
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma) :
    Steps77Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
  have hGA := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  have hK108 : F10.K108H207 := F10.k108H207_holds
  have hK331 : InS3.K331 := InS3.k331_of_residue InS3.k331Residue_holds
  have hGy : Global22yNo := global22yNo_holds
  have hGi : Global22i :=
    { toGlobal22e := hGy.toGlobal22e
      griess := hGy.griess
      nativeGriess := hGy.nativeGriess
      exclRes := ⟨uc22pwlie_lin_holds, uc22pwliu_unitary_holds, uc22pwliu_u54_holds,
        uc22pwex_e_holds⟩
      twoRes := ⟨uc22pwlie_lin3_holds, uc22pwliu_unitary3_holds,
        uc22pwex_d4_holds hGy.nativeGriess, uc22pwex_f4_holds hGy.nativeGriess,
        uc22pwex_d4two_holds hGy.nativeGriess⟩
      diagram := uc22p20uDiagramInput_holds }
  have hGh : Global22h := hGi.toGlobal22h
  have hGe : Global22e := hGh.toGlobal22g.toGlobal22e
  have hF22f : Global22f :=
    uc22p20r_global22f_of_tables hGh.griess hGh.nativeGriess hGh.excl hGh.two
  have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
    PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
      UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
  have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
  have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
  have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
  have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
  have h82 := PartTwo.Three.r82_dataOfSetup hGF hS hUC hC S hMS
  have hJ4 := PartTwo.Three.r880J4_dataOfSetup hS hUC hC S
  have h869N := F08.R869N_of_R869 _ (PartTwo.Three.r869_dataOfSetup_of_inputs hGF hS hUC hC S hMS)
  have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h82 hJ4
  have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
    uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
  have h211 : ∀ Ch : Choice2011 G, S21_1 (PartTwo.Three.dataOfSetup hS S) Ch := fun Ch =>
    uc22p22r_s21_1_of_k108H207 _ Ch hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
  have hn3 : ∀ Ch : Choice2011 G, H1930 (PartTwo.Three.dataOfSetup hS S) →
      ∀ c : Ctx21 (PartTwo.Three.dataOfSetup hS S) Ch, 3 ≤ c.n := fun Ch =>
    uc22p20g_hn3_of hGy.excFacts _ Ch h207
  have h5 : ∀ Ch : Choice2011 G, S21_5 (PartTwo.Three.dataOfSetup hS S) Ch := fun Ch =>
    s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S h82
      (s21_15Two_of_certificate113 _ _ (h211 Ch) hSg (uc22r899e3_dataOfSetup hS hUC S))
  have h3NN4 : S21_3RestNN4 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
    s21_3RestNN4_of_tables CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
      (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .M22) UCK.k32_holds
      CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
  have h3NN := s21_3RestNN_dataOfSetup_of_restNN4 hSE5 hSE3 hS hUC hC hGy.k36 S _ h3NN4
  have h3 := s21_3_dataOfSetup_of_restNN hSQ hSE5 hSE3 hS S h82 h869N _ h3NN
  have hKF7 := kf7Use_dataOfSetup hSQ hSE5 hSE3 hS S
  have h72 := PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S
  have h218 : ∀ Ch : Choice2011 G, S21_8N (PartTwo.Three.dataOfSetup hS S) Ch := fun Ch =>
    s21_8N_dataOfSetup hSE3 hGA PartTwo.S19.k_19_25_noL2SzSection_holds hS hUC hC S (h211 Ch)
      h614 h76 h72 (s21_8K_dataOfSetup hS S (h211 Ch) h614 h76)
  have h218UR : ∀ Ch : Choice2011 G, S21_8UR (PartTwo.Three.dataOfSetup hS S) Ch := fun Ch =>
    s21_8UR_dataOfSetup hS hUC hC S (h211 Ch) h614 h76 h72
      PartTwo.S19.k_19_25_noL2SzSection_holds
  have h15C : S21_15C (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
    s21_15C_of (h211 _) hSg (PartTwo.Three.r77E2_dataOfSetup hSE5 hSE3 hS S) h614
  have hU2 : R8100U2 (PartTwo.Three.dataOfSetup hS S) :=
    r8100U2_dataOfSetup_of_normalizer_le hS hUC S (r8100Step_of_r847E3ThinNNTwo
      (r847E3ThinNNTwo_dataOfSetup hSE5 PartOne.Section7.stronglyEmbeddedFiveZ_holds
        PartTwo.thinList13_holds hSQ hSE3 hG3 CFSG.AGLEmbedding.kFactReeInvolution hS S))
  have h869S5 : F08.R869NS5 (PartTwo.Three.dataOfSetup hS S) :=
    PartTwo.Three.r869NS5_dataOfSetup hSQ.toStronglyEmbeddedSolvable hSE5 hSE3 hS S
  have h14 : S21_14 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
    s21_14_of_residuals hGA hGy.nativeGriess hSg h614 h76 h82
      (fun _ hq hq2 => PartTwo.Three.pRank_le_three_dataOfSetup hS S hq hq2 le_rfl)
      (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S) (hn3 _) h3 (h5 _) (h218 _)
      (s21_8XT_dataOfSetup hS hUC hC S hMS (h211 _) h614 h76) (s21_14R4T_holds _ _)
      (s21_14R3LF_dataOfSetup hGA hS hUC S (F07.r74Card_dataOfSetup hSE5 hSE3 hS hUC hC S))
      (s21_14R3LK2_dataOfSetup hGA hS hUC S (h211 _))
      (s21_14D4T_dataOfSetup hS hUC hC S hMS) (s21_14K2T_dataOfSetup hGF hS hUC hC S hMS)
  have hL3PTwo : S21_12aFR34L3PTwo (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S)) :=
    s21_12aFR34L3PTwo_dataOfSetup hS hUC hC S hMS
  have hEv2 : S21_12aFR34F2Even2 (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S)) :=
    s21_12aFR34F2Even2_dataOfSetup hGA hS S hKF7 (hn3 _) (h5 _) h82 (h211 _)
  obtain ⟨h16, h17, h8107⟩ :=
    s21_16_17_dataOfSetup hS hUC hC S hK hK332 hGA hSQ hSE5 hSE3 hSg h614 h76 h82 h869N h207
      (h211 _) (hn3 _) (h5 _) h3 hKF7 h14 hL3PTwo hEv2
  have h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S) :=
    r847E3Thin_dataOfSetup hSE5 PartOne.Section7.stronglyEmbeddedFiveZ_holds
      PartTwo.thinList13_holds hGy.cyclicSylowThreeOutAbelian hG3
      CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
  exact
    { s21_14 := h14
      s22_5_1RStarSn := s22_5_1RStarSn_dataOfSetup hS hUC hC S hMS
      s21_12aR34L3P := s21_12aFR34L3P_of_res_two (hn3 _)
        (uc22s2112l3p_of_inputs hGA hSg hKF7 (h5 _) (r149L3P_dataOfSetup hS hUC hC S))
        hL3PTwo
      s21_12aR34F2Q35 := s21_12aFR34F2Q35_of_kfacts kFieldAutOdd_holds kq35NormSylowAlpha_holds
        kQ35PermFive_holds hSg (hn3 (fun _ _ => True)) (h5 _) (fun _ _ _ => trivial)
      s21_12aR34F2Even := s21_12aFR34F2Even_of_f2Even2 kFieldAutOdd_holds kFunSplit_holds
        kFunCount_holds hGA hSg hKF7 (hn3 (fun _ _ => True)) (h5 _) h82 (h211 _)
        (fun _ _ _ => trivial) hEv2
      r8_2 := h82
      r8_69NRest3 := F08.R869NRest3_of_R869N _ h869N
      r8_69MConsRest3 := PartTwo.Three.r869MConsRest3_dataOfSetup hS S
      r8_80J4 := hJ4
      s21_22R3F3SzQ5T := s21_22R3F3SzQ5T_dataOfSetup hS hUC hC S hMS
      s21_22R3E5R := s21_22R3E5R_of_s21_22R3E5R2 hSg h869S5 h15C hU2
        (uc22r3e5c_s21_22R3E5R2_of_inputs
          (Standing22.ofSetup hS hUC hC hGy.k36 S hMS) hSg
          (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S) (h5 _) h15C
          (PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S) kStrongEmbedded72_holds hU2
          (h211 _) h869S5 h82 h8107 h847T h16 h17 (hn3 _))
      s21_22R3NoPairR := s21_22R3NoPairR_dataOfSetup hS hUC hC S hMS hSE3 (h211 _) (hn3 _)
        (h218 _) (h218UR _) }

theorem notTIStage1930_three
    (hGF : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause) (hS : Standing G)
    (hC : AGL81TheoremC G) : CFSG.LocalAnalysis.RankThreeUC.NotTIStage1930 G := by
  intro hUC
  exact notTIStage1930_of_steps77Three hS hC (F10.k105SporRest_of_restB
      (F10.k105SporRestB_of_restE F10.k105SporRestE_holds)) kFieldAutOdd_holds
    kFunSplit_holds kFunCount_holds (fun S hMS => steps77Three_dataOfSetup hGF
      (F10.k105SporRest_of_restB (F10.k105SporRestB_of_restE F10.k105SporRestE_holds))
      (UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
        (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds))
      hS hUC hC S hMS)
    hUC


end CFSG.LocalAnalysis.UniquenessCase.UC22
