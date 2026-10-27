module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps77Three
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.RankThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Main
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSetupThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R77EqThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.S206ThreeJ4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.S2117PowThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NoL2SzSectionHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsSixteen
import CFSG.LocalAnalysis.UniquenessCase.UC1K462Holds
import CFSG.LocalAnalysis.UniquenessCase.UC1ZassMain
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KThin
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22K108HCore
import CFSG.LocalAnalysis.UniquenessCase.UC22K108Holds
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Holds
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Residue
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutSetup
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22R847O3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112E3NN
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aE3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Ident
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S216
import CFSG.LocalAnalysis.UniquenessCase.UC22S217RJ1U
import CFSG.LocalAnalysis.UniquenessCase.UC22S217Sp4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Uc
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Main
import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33
import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsHolds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R913A5S
import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5Holds
import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5NHolds
import CFSG.LocalAnalysis.UniquenessCase.UCFront09x
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRest
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R846Three
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Dvd
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3SU3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2119G4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3B
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3R78p3
import CFSG.LocalAnalysis.UniquenessCase.UC22S219G4
import CFSG.LocalAnalysis.UniquenessCase.UC22Steps68Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R77E2Three
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229S15C
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsRest
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DProof
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Three

theorem notTIStage1930_of_steps77Three
    {G : Type} [Group G] [Finite G]
    (hS : RankThreeUC.Standing G) (hC : RankThreeUC.AGL81TheoremC G) (hK : F10.K105SporRest)
    (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount)
    (h : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps77Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) :
    RankThreeUC.NotTIStage1930 G := by
  intro hUC
  have steps76 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps76Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hK5 : F10.K105Spor := F10.k105Spor_of_rest hK
    have hK332 : UCK.K332Cyc :=
      UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
        (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds)
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
    have hSt := h S hMS
    have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 hSt.r8_2 hSt.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have hn3 := uc22p20g_hn3_of hGy.excFacts (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) h207
    have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hSS := hSQ.toStronglyEmbeddedSolvable
    have h869N := PartTwo.Three.r869N_dataOfSetup_of_rest3 hSS hSE5 hSE3 hS hUC hC S hSt.r8_69NRest3
    have h869M := PartTwo.Three.r869MCons_dataOfSetup_of_rest3 hSE5 hSE3 hS hUC hC S
      hSt.r8_69MConsRest3
    have h15T := s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S)
    have h5 := s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S hSt.r8_2 h15T
    have h3NN4 : S21_3RestNN4 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_3RestNN4_of_tables CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
        CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
        (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .M22) UCK.k32_holds
        CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
    have h3NN := s21_3RestNN_dataOfSetup_of_restNN4 hSE5 hSE3 hS hUC hC hGy.k36 S _ h3NN4
    have h3 := s21_3_dataOfSetup_of_restNN hSQ hSE5 hSE3 hS S hSt.r8_2 h869N _ h3NN
    have h6 := s21_6Inf_of_k105Spor h3 h5 hn3 hK5 hrank hout
    have h8107 := R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg hSt.r8_2
      (R847O3.r847OrderThree_dataOfSetup hSE5 hSEZ KBridge.kThinSimple_holds hS S hSg) h76 h614
    have h920J1 := PartOne.Section9.r920J1_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds hS S hSt.r8_2 h614
    have h920odd := PartOne.Section9.r920odd_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      UCK.Zass.zassenhausPerfect_holds hS S hSt.r8_2 h614
    have h7 : 7 ∉ (PartTwo.Three.dataOfSetup hS S).sig →
        CFSG.Open.pRank 7 (PartTwo.Three.dataOfSetup hS S).M ≤ 2 := fun h7σ =>
      Nat.le_of_not_lt fun h7' => h7σ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC
        S.witness.maxLocal (by norm_num) le_rfl h7')
    have h17J := s21_17RJ1_of_three _ _ h211 h5 hn3 h6 hSg h8107 h920J1 h7
    have h847T := r847E3Thin_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have hKF7 := kf7Use_dataOfSetup hSQ hSE5 hSE3 hS S
    have hR34 := s21_12aFR34_dataOfSetup_of_l3P_q35_even hKF1 hKS hKC
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hS hUC S hKF7 hn3 h5
      hSt.r8_2 h211 (fun _ _ _ => trivial) hSt.s21_12aR34L3P hSt.s21_12aR34F2Q35
      hSt.s21_12aR34F2Even
    have h12 : S21_12R3 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_12R3_dataOfSetup_of_s21_12aF hSQ hSE5 hSEZ hSE3 KBridge.kThinSimple_holds
        PartTwo.thinList13_holds hS hUC S hSt.r8_2 h211
        (s21_12aF_dataOfSetup_of_s21_12aFR34 hSQ hSE5 hSE3 KBridge.kThinSimple_holds hGy.excFacts
          hGh.listB_nonabelian CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
          PartTwo.thinList13_holds PartTwo.Inputs1719.k_LieModelNotL2_holds hGy.griess hS hUC hC S
          h207 h211 h3 hSt.r8_2 h614 hR34)
    have h212 := s21_12_of_s21_12R3 h5 hSg h847T h3
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput PartTwo.thinList13_holds
      PartTwo.Inputs1719.k_LieModelNotL2_holds h12
    have h16 : S21_16 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_16_of_s21_6Inf h6 h212 (s21_13_of h3 h5 hn3) hSt.s21_14
        CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
    have h17 : S21_17 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_17_of_residualT hS.rank hGy.griess h211
        (PartTwo.Three.s21_17R_one_pow_of_three hS.rank hGy.griess _ _) hSg
        (conclusion76_of_r76Sig h76) h16 h15T (s21_normalSp4_of _ _ hSg h211)
        (s21_17RT_of_s21_17RT2 h212 h869N hn3
          (s21_17RT2_of_s21_17RJ1 hS.rank hSE3 hSt.r8_2 hn3 h17J))
    have h8 := s21_8Sp4_of_s21_8U hSg h211 (s21_8U_dataOfSetup hS hUC hC S h211 h614 h76
      (PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S) PartTwo.S19.k_19_25_noL2SzSection_holds)
    have hs := Standing22.ofSetup hS hUC hC hGy.k36 S hMS
    have hid := uc22p22q_r613ident_of _ hs.sigma23 hs.r6_1 hs.sigma2
    have haut := uc22p22q_r613aut_of _ hs.sigma23 hs.r6_1 hs.sigma2 hs.cent
    have h119 : R119W (PartTwo.Three.dataOfSetup hS S) :=
      uc22p22u_r119W _ (uc22p22u_r118W PartTwo.thinList13_holds hGy.cyclicSylowThreeOutAbelian _
        (uc22p22u_c116W _ hSg hs.r6_1 hs.r6_3 (PartTwo.Three.r77Eq_dataOfSetup hSE5 hSE3 hS hUC S)
          (uc22p22q_r111_of _ hs.sigma23 hs.r6_1 hs.r6_11)
          (uc22p22q_r112_of _ hs.sigma23 hs.r6_1 hs.sigma2 hid hs.cent haut))
        (uc22p22u_c117W_of_R869MCons _ h869M))
    have h31 : S22_3_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      uc22p22p_s22_3_1_of _ _ (UC6.r6_40_2_holds hGy.u2 hGy.s25 _) fun _ c =>
        (uc22p22n_inCalV1_of_not_isTI _ hs.dataExt hs.r6_1 (uc22p22e_inCalV_U _) c.hU).2
    have h33 := uc22p22wj_s22_3_of_sp4 hGy.k148 _ _ hs.dataExt hs.r6_1 h31 h119 h16 h8
    have h92D := F09.r92_of_inputs UCK.k32_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartTwo.Three.dataOfSetup hS S)
    have h923 : F09.R923 (PartTwo.Three.dataOfSetup hS S) :=
      F09.r923_holds_of_r913A5S hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        F09.kFactShape92NoFaithfulA5_holds hK332
        (CFSG.CGT.PushingUpLit.CGT6.aschbacherSixThreeCore_of_embeddingK
          CFSG.HardMathSupport.Foote.Coordinator.aschbacherEmbeddingK_proved)
        _ hSg (UC6.r6_40_1_holds hGy.u2 hGy.s25 _) h92D
        (F09.r913A5S_holds F09.kFactShape92A5Normalizer_holds _ h92D)
    have h847L3 := r847E3L3_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have h2014 := s20_14N_of_strongParab207 hGh.listB_nonabelian hr66 h204 h207
      uc22sp207_strongParab207
    exact hSt.toSteps76Three hs.dataExt hs.r6_1 h119 h17 h211 h212 h31 h33.2 hn3 hSg h847L3 h920odd
      h923 h8107 h16 h2014 hKF1 hKS hKC
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hUC hKF7 h5
      (fun _ _ _ => trivial)

  have steps75 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps75Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hK5 : F10.K105Spor := F10.k105Spor_of_rest hK
    have hK332 : UCK.K332Cyc :=
      UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
        (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds)
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
    have hSt := steps76 S hMS
    have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 hSt.r8_2 hSt.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have hn3 := uc22p20g_hn3_of hGy.excFacts (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) h207
    have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hSS := hSQ.toStronglyEmbeddedSolvable
    have h869N := PartTwo.Three.r869N_dataOfSetup_of_rest3 hSS hSE5 hSE3 hS hUC hC S hSt.r8_69NRest3
    have h15T := s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S)
    have h5 := s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S hSt.r8_2 h15T
    have h3NN4 : S21_3RestNN4 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_3RestNN4_of_tables CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
        CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
        (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .M22) UCK.k32_holds
        CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
    have h3NN := s21_3RestNN_dataOfSetup_of_restNN4 hSE5 hSE3 hS hUC hC hGy.k36 S _ h3NN4
    have h3 := s21_3_dataOfSetup_of_restNN hSQ hSE5 hSE3 hS S hSt.r8_2 h869N _ h3NN
    have h6 := s21_6Inf_of_k105Spor h3 h5 hn3 hK5 hrank hout
    have h8107 := R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg hSt.r8_2
      (R847O3.r847OrderThree_dataOfSetup hSE5 hSEZ KBridge.kThinSimple_holds hS S hSg) h76 h614
    have h920J1 := PartOne.Section9.r920J1_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds hS S hSt.r8_2 h614
    have h920odd := PartOne.Section9.r920odd_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      UCK.Zass.zassenhausPerfect_holds hS S hSt.r8_2 h614
    have h7 : 7 ∉ (PartTwo.Three.dataOfSetup hS S).sig →
        CFSG.Open.pRank 7 (PartTwo.Three.dataOfSetup hS S).M ≤ 2 := fun h7σ =>
      Nat.le_of_not_lt fun h7' => h7σ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC
        S.witness.maxLocal (by norm_num) le_rfl h7')
    have h17J := s21_17RJ1_of_three _ _ h211 h5 hn3 h6 hSg h8107 h920J1 h7
    have h847T := r847E3Thin_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have hF3 : S21_12aFR34F3 (PartTwo.Three.dataOfSetup hS S)
        (Choice214U (PartTwo.Three.dataOfSetup hS S)) :=
      s21_12aFR34F3_dataOfSetup hS S
    have hL3 : S21_12aFR34L3 (PartTwo.Three.dataOfSetup hS S)
        (Choice214U (PartTwo.Three.dataOfSetup hS S)) :=
      s21_12aFR34L3_dataOfSetup_of_l3P hS S hSt.s21_12aR34L3P
    have hR34 := s21_12aFR34_of_rest
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hSt.r8_2 h211
      (fun _ _ _ => trivial) hL3 hSt.s21_12aR34F2 hF3
    have h12 : S21_12R3 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_12R3_dataOfSetup_of_s21_12aF hSQ hSE5 hSEZ hSE3 KBridge.kThinSimple_holds
        PartTwo.thinList13_holds hS hUC S hSt.r8_2 h211
        (s21_12aF_dataOfSetup_of_s21_12aFR34 hSQ hSE5 hSE3 KBridge.kThinSimple_holds hGy.excFacts
          hGh.listB_nonabelian CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
          PartTwo.thinList13_holds PartTwo.Inputs1719.k_LieModelNotL2_holds hGy.griess hS hUC hC S
          h207 h211 h3 hSt.r8_2 h614 hR34)
    have h212 := s21_12_of_s21_12R3 h5 hSg h847T h3
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput PartTwo.thinList13_holds
      PartTwo.Inputs1719.k_LieModelNotL2_holds h12
    have h16 : S21_16 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_16_of_s21_6Inf h6 h212 (s21_13_of h3 h5 hn3) hSt.s21_14
        CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
    have h17 : S21_17 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_17_of_residualT hS.rank hGy.griess h211
        (PartTwo.Three.s21_17R_one_pow_of_three hS.rank hGy.griess _ _) hSg
        (conclusion76_of_r76Sig h76) h16 h15T (s21_normalSp4_of _ _ hSg h211)
        (s21_17RT_of_s21_17RT2 h212 h869N hn3
          (s21_17RT2_of_s21_17RJ1 hS.rank hSE3 hSt.r8_2 hn3 h17J))
    have h846 := PartTwo.Three.r846_dataOfSetup hGy.griess hSE5 hSE3 hS hUC hC hGy.k36 S
    have h847S := r847E3SU3_dataOfSetup_of_dvd hSE5 hSEZ hG3 CFSG.AGLEmbedding.kFactReeInvolution
      hSE3 hGy.griess uc22pwCartanSU3_holds uc22pwTorusSU3_holds hS S h846
      (r847E3Dvd_dataOfSetup hSE5 hSEZ hGy.griess hS S)
    have h18 := s21_18_of _ _ h17 hGe.toGlobal22d.toGlobal22b.schreier
    have h2119 := s21_19_of_r847E3Thin _ _ h211 h212 h8107 h847T hS.rank h920odd hSg.nonempty hn3
    have h219 := s21_9Sig3_dataOfSetup_of_r847E3SU3 hGy.griess hSE5 hSE3 hS hUC hC S h211 h846 h847S
    have h78 := PartTwo.Three.r7_8R3p3_dataOfSetup hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS
      hUC hC S
    have hs := Standing22.ofSetup hS hUC hC hGy.k36 S hMS
    exact hSt.toSteps75Three CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement h211
      (fun _ _ _ => trivial) hL3 hF3 h3NN4 hs (UCK.u3Center_of_griess hGy.griess) h846 h219 h17
      (s21_21U3_three_of_r847E3 hSE5 PartTwo.thinList13_holds hGy.cyclicSylowThreeOutAbelian hS hUC
        S h78 hSt.r8_2 h846 h847T h847S h211 h16 h18 h2119 h219)
      hn3

  have steps74 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps74Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hK5 : F10.K105Spor := F10.k105Spor_of_rest hK
    have hK332 : UCK.K332Cyc :=
      UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
        (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds)
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
    have h75 := steps75 S hMS
    have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h75.r8_2 h75.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have hn3 := uc22p20g_hn3_of hGy.excFacts (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) h207
    have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hSS := hSQ.toStronglyEmbeddedSolvable
    have h869N := PartTwo.Three.r869N_dataOfSetup_of_rest3 hSS hSE5 hSE3 hS hUC hC S h75.r8_69NRest3
    have h869M := PartTwo.Three.r869MCons_dataOfSetup_of_rest3 hSE5 hSE3 hS hUC hC S
      h75.r8_69MConsRest3
    have h15T := s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S)
    have h5 := s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S h75.r8_2 h15T
    have h3NN := s21_3RestNN_dataOfSetup_of_restNN4 hSE5 hSE3 hS hUC hC hGy.k36 S _ h75.s21_3NN4
    have h3 := s21_3_dataOfSetup_of_restNN hSQ hSE5 hSE3 hS S h75.r8_2 h869N _ h3NN
    have h6 := s21_6Inf_of_k105Spor h3 h5 hn3 hK5 hrank hout
    have h8107 := R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg h75.r8_2
      (R847O3.r847OrderThree_dataOfSetup hSE5 hSEZ KBridge.kThinSimple_holds hS S hSg) h76 h614
    have h920J1 := PartOne.Section9.r920J1_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds hS S h75.r8_2 h614
    have h920odd := PartOne.Section9.r920odd_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      UCK.Zass.zassenhausPerfect_holds hS S h75.r8_2 h614
    have h7 : 7 ∉ (PartTwo.Three.dataOfSetup hS S).sig →
        CFSG.Open.pRank 7 (PartTwo.Three.dataOfSetup hS S).M ≤ 2 := fun h7σ =>
      Nat.le_of_not_lt fun h7' => h7σ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC
        S.witness.maxLocal (by norm_num) le_rfl h7')
    have h17J := s21_17RJ1_of_three _ _ h211 h5 hn3 h6 hSg h8107 h920J1 h7
    have h847T := r847E3Thin_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have h12 : S21_12R3 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_12R3_dataOfSetup_of_s21_12aF hSQ hSE5 hSEZ hSE3 KBridge.kThinSimple_holds
        PartTwo.thinList13_holds hS hUC S h75.r8_2 h211
        (s21_12aF_dataOfSetup_of_s21_12aFR34 hSQ hSE5 hSE3 KBridge.kThinSimple_holds hGy.excFacts
          hGh.listB_nonabelian CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
          PartTwo.thinList13_holds PartTwo.Inputs1719.k_LieModelNotL2_holds hGy.griess hS hUC hC S
          h207 h211 h3 h75.r8_2 h614 h75.s21_12aR34)
    have h212 := s21_12_of_s21_12R3 h5 hSg h847T h3
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput PartTwo.thinList13_holds
      PartTwo.Inputs1719.k_LieModelNotL2_holds h12
    have h16 : S21_16 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_16_of_s21_6Inf h6 h212 (s21_13_of h3 h5 hn3) h75.s21_14
        CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
    have h17 : S21_17 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_17_of_residualT hS.rank hGy.griess h211
        (PartTwo.Three.s21_17R_one_pow_of_three hS.rank hGy.griess _ _) hSg
        (conclusion76_of_r76Sig h76) h16 h15T (s21_normalSp4_of _ _ hSg h211)
        (s21_17RT_of_s21_17RT2 h212 h869N hn3
          (s21_17RT2_of_s21_17RJ1 hS.rank hSE3 h75.r8_2 hn3 h17J))
    have h15 := s21_15C_of h211 hSg (PartTwo.Three.r77E2_dataOfSetup hSE5 hSE3 hS S) h614
    have h8 := s21_8Sp4_of_s21_8U hSg h211 (s21_8U_dataOfSetup hS hUC hC S h211 h614 h76
      (PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S) PartTwo.S19.k_19_25_noL2SzSection_holds)
    have hs := Standing22.ofSetup hS hUC hC hGy.k36 S hMS
    have hid := uc22p22q_r613ident_of _ hs.sigma23 hs.r6_1 hs.sigma2
    have haut := uc22p22q_r613aut_of _ hs.sigma23 hs.r6_1 hs.sigma2 hs.cent
    have h119 : R119W (PartTwo.Three.dataOfSetup hS S) :=
      uc22p22u_r119W _ (uc22p22u_r118W PartTwo.thinList13_holds hGy.cyclicSylowThreeOutAbelian _
        (uc22p22u_c116W _ hSg hs.r6_1 hs.r6_3 (PartTwo.Three.r77Eq_dataOfSetup hSE5 hSE3 hS hUC S)
          (uc22p22q_r111_of _ hs.sigma23 hs.r6_1 hs.r6_11)
          (uc22p22q_r112_of _ hs.sigma23 hs.r6_1 hs.sigma2 hid hs.cent haut))
        (uc22p22u_c117W_of_R869MCons _ h869M))
    have h31 : S22_3_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      uc22p22p_s22_3_1_of _ _ (UC6.r6_40_2_holds hGy.u2 hGy.s25 _) fun _ c =>
        (uc22p22n_inCalV1_of_not_isTI _ hs.dataExt hs.r6_1 (uc22p22e_inCalV_U _) c.hU).2
    have h33 := uc22p22wj_s22_3_of_sp4 hGy.k148 _ _ hs.dataExt hs.r6_1 h31 h119 h16 h8
    have h92D := F09.r92_of_inputs UCK.k32_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartTwo.Three.dataOfSetup hS S)
    have h923 : F09.R923 (PartTwo.Three.dataOfSetup hS S) :=
      F09.r923_holds_of_r913A5S hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        F09.kFactShape92NoFaithfulA5_holds hK332
        (CFSG.CGT.PushingUpLit.CGT6.aschbacherSixThreeCore_of_embeddingK
          CFSG.HardMathSupport.Foote.Coordinator.aschbacherEmbeddingK_proved)
        _ hSg (UC6.r6_40_1_holds hGy.u2 hGy.s25 _) h92D
        (F09.r913A5S_holds F09.kFactShape92A5Normalizer_holds _ h92D)
    have h847L3 := r847E3L3_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have hNN := r847E3ThinNNOut_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds hS S
    exact h75.toSteps74Three hs.dataExt hs.r6_1 h119 h17 h211 h212 h31 h33.2 hn3 hSg h847L3 h920odd
      h923 h8107 h3NN h15 hNN

  have steps73 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps73Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hK5 : F10.K105Spor := F10.k105Spor_of_rest hK
    have hK332 : UCK.K332Cyc :=
      UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
        (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds)
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
    have h74 := steps74 S hMS
    have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h74.r8_2 h74.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have hn3 := uc22p20g_hn3_of hGy.excFacts (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) h207
    have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hSS := hSQ.toStronglyEmbeddedSolvable
    have h869N := PartTwo.Three.r869N_dataOfSetup_of_rest3 hSS hSE5 hSE3 hS hUC hC S h74.r8_69NRest3
    have h869M := PartTwo.Three.r869MCons_dataOfSetup_of_rest3 hSE5 hSE3 hS hUC hC S
      h74.r8_69MConsRest3
    have h15T := s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S)
    have h5 := s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S h74.r8_2 h15T
    have h3 := s21_3_dataOfSetup_of_restNN hSQ hSE5 hSE3 hS S h74.r8_2 h869N _ h74.s21_3NN
    have h6 := s21_6Inf_of_k105Spor h3 h5 hn3 hK5 hrank hout
    have h8107 := R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg h74.r8_2
      (R847O3.r847OrderThree_dataOfSetup hSE5 hSEZ KBridge.kThinSimple_holds hS S hSg) h76 h614
    have h920J1 := PartOne.Section9.r920J1_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds hS S h74.r8_2 h614
    have h920odd := PartOne.Section9.r920odd_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      UCK.Zass.zassenhausPerfect_holds hS S h74.r8_2 h614
    have h7 : 7 ∉ (PartTwo.Three.dataOfSetup hS S).sig →
        CFSG.Open.pRank 7 (PartTwo.Three.dataOfSetup hS S).M ≤ 2 := fun h7σ =>
      Nat.le_of_not_lt fun h7' => h7σ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC
        S.witness.maxLocal (by norm_num) le_rfl h7')
    have h17J := s21_17RJ1_of_three _ _ h211 h5 hn3 h6 hSg h8107 h920J1 h7
    have h847T := r847E3Thin_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have h12 : S21_12R3 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_12R3_dataOfSetup_of_s21_12aF hSQ hSE5 hSEZ hSE3 KBridge.kThinSimple_holds
        PartTwo.thinList13_holds hS hUC S h74.r8_2 h211
        (s21_12aF_dataOfSetup_of_s21_12aFR34 hSQ hSE5 hSE3 KBridge.kThinSimple_holds hGy.excFacts
          hGh.listB_nonabelian CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
          PartTwo.thinList13_holds PartTwo.Inputs1719.k_LieModelNotL2_holds hGy.griess hS hUC hC S
          h207 h211 h3 h74.r8_2 h614 h74.s21_12aR34)
    have h212 := s21_12_of_s21_12R3 h5 hSg h847T h3
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput PartTwo.thinList13_holds
      PartTwo.Inputs1719.k_LieModelNotL2_holds h12
    have h16 : S21_16 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_16_of_s21_6Inf h6 h212 (s21_13_of h3 h5 hn3) h74.s21_14
        CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
    have h17 : S21_17 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_17_of_residualT hS.rank hGy.griess h211
        (PartTwo.Three.s21_17R_one_pow_of_three hS.rank hGy.griess _ _) hSg
        (conclusion76_of_r76Sig h76) h16 h15T (s21_normalSp4_of _ _ hSg h211)
        (s21_17RT_of_s21_17RT2 h212 h869N hn3
          (s21_17RT2_of_s21_17RJ1 hS.rank hSE3 h74.r8_2 hn3 h17J))
    have h15 := s21_15C_of h211 hSg (PartTwo.Three.r77E2_dataOfSetup hSE5 hSE3 hS S) h614
    have h13 := PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S
    have h8 := s21_8Sp4_of_s21_8U hSg h211 (s21_8U_dataOfSetup hS hUC hC S h211 h614 h76
      (PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S) PartTwo.S19.k_19_25_noL2SzSection_holds)
    have hs := Standing22.ofSetup hS hUC hC hGy.k36 S hMS
    have hid := uc22p22q_r613ident_of _ hs.sigma23 hs.r6_1 hs.sigma2
    have haut := uc22p22q_r613aut_of _ hs.sigma23 hs.r6_1 hs.sigma2 hs.cent
    have h119 : R119W (PartTwo.Three.dataOfSetup hS S) :=
      uc22p22u_r119W _ (uc22p22u_r118W PartTwo.thinList13_holds hGy.cyclicSylowThreeOutAbelian _
        (uc22p22u_c116W _ hSg hs.r6_1 hs.r6_3 (PartTwo.Three.r77Eq_dataOfSetup hSE5 hSE3 hS hUC S)
          (uc22p22q_r111_of _ hs.sigma23 hs.r6_1 hs.r6_11)
          (uc22p22q_r112_of _ hs.sigma23 hs.r6_1 hs.sigma2 hid hs.cent haut))
        (uc22p22u_c117W_of_R869MCons _ h869M))
    have h31 : S22_3_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      uc22p22p_s22_3_1_of _ _ (UC6.r6_40_2_holds hGy.u2 hGy.s25 _) fun _ c =>
        (uc22p22n_inCalV1_of_not_isTI _ hs.dataExt hs.r6_1 (uc22p22e_inCalV_U _) c.hU).2
    have h33 := uc22p22wj_s22_3_of_sp4 hGy.k148 _ _ hs.dataExt hs.r6_1 h31 h119 h16 h8
    have h92D := F09.r92_of_inputs UCK.k32_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartTwo.Three.dataOfSetup hS S)
    have h923 : F09.R923K1 (PartTwo.Three.dataOfSetup hS S) :=
      F09.r923K1_holds_of_r913A5S hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        F09.kFactShape92NoFaithfulA5_holds
        (CFSG.CGT.PushingUpLit.CGT6.aschbacherSixThreeCore_of_embeddingK
          CFSG.HardMathSupport.Foote.Coordinator.aschbacherEmbeddingK_proved)
        _ (UC6.r6_40_1_holds hGy.u2 hGy.s25 _) h92D
        (F09.r913A5S_holds F09.kFactShape92A5Normalizer_holds _ h92D)
    have h847L3 := r847E3L3_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have h1 := s22_5_1K1_of_inputsE3 _ _ hs.dataExt hs.r6_1 h33.2 h119 h17 h211 hn3 h847L3
      h920odd h923 h212
    have h8100 : R8100U2 (PartTwo.Three.dataOfSetup hS S) :=
      r8100U2_dataOfSetup_of_normalizer_le hS hUC S (r8100Step_of_r847E3ThinNNTwo
        (r847E3ThinNNTwo_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds hSQ hSE3 hG3
          CFSG.AGLEmbedding.kFactReeInvolution hS S))
    have h202 := s20_2_of (PartTwo.Three.dataOfSetup hS S) hGe.k318 h201
    have h205 := s20_5_of (PartTwo.Three.dataOfSetup hS S) h202
      (s20_3_of _ h201 h202 hGe.listB_nonabelian hGe.schreier hGe.dichotomy
        (uc22p20h_five _ hGe.threeNoncentral))
      hGe.listB_nonabelian hGe.listB_notSmall
    have h2014 := s20_14N_of_strongParab207 hGh.listB_nonabelian hr66 h204 h207
      uc22sp207_strongParab207
    exact h74.toSteps73Three h1 h12 h3 h869N h869M hSg h13 h211 h8107 h15 h847T h16 h17 hn3 h8100
      h2014 hGh.listB_nonabelian h205

  have steps72 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps72Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
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
    have h73 := steps73 S hMS
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have h8107 := R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg h73.r8_2
      (R847O3.r847OrderThree_dataOfSetup hSE5 hSEZ KBridge.kThinSimple_holds hS S hSg) h76 h614
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h73.r8_2 h73.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have h15 := s21_15C_of h211 hSg (PartTwo.Three.r77E2_dataOfSetup hSE5 hSE3 hS S) h614
    have h8100 := r8100U2_dataOfSetup_of_r8100U2D hSE5 hSEZ hG3 CFSG.AGLEmbedding.kFactReeInvolution
      hSE3 hS hUC S h73.r8_100U2D
    exact h73.toSteps72Three h8107 hSg h15 h8100

  have steps71 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps71Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
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
    have h72 := steps72 S hMS
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h72.r8_2 h72.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    exact h72.toSteps71Three (s21_8U_dataOfSetup hS hUC hC S h211 h614 h76
      (PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S) PartTwo.S19.k_19_25_noL2SzSection_holds)

  have steps70 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps70Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
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
    have h71 := steps71 S hMS
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h71.r8_2 h71.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have h15 := s21_15C_of h211 hSg (PartTwo.Three.r77E2_dataOfSetup hSE5 hSE3 hS S)
      (UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S)
    have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
    have h8100 := r8100U2_dataOfSetup_of_r8100U2D hSE5 hSEZ hG3 CFSG.AGLEmbedding.kFactReeInvolution
      hSE3 hS hUC S h71.r8_100U2D
    exact h71.toSteps70Three hSg (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S) h211 h15
      h8100

  have steps67 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps67Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hK5 : F10.K105Spor := F10.k105Spor_of_rest hK
    intro S hMS
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
    have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have h70 := steps70 S hMS
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h70.r8_2 h70.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have hn3 := uc22p20g_hn3_of hGy.excFacts (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) h207
    have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have h15T := s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S)
    have h5 := s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S h70.r8_2 h15T
    have h3 := h70.s21_3
    have h6 := s21_6Inf_of_k105Spor h3 h5 hn3 hK5 hrank hout
    have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
    have h8107 := R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg h70.r8_2
      (R847O3.r847OrderThree_dataOfSetup hSE5 hSEZ KBridge.kThinSimple_holds hS S hSg) h76 h614
    have h920J1 := PartOne.Section9.r920J1_dataOfSetup hSQ hSE5 hSE3 (UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
        (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds)) UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds hS S h70.r8_2 h614
    have h920odd := PartOne.Section9.r920odd_dataOfSetup hSQ hSE5 hSE3 (UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
        (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds)) UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      UCK.Zass.zassenhausPerfect_holds hS S h70.r8_2 h614
    have h7 : 7 ∉ (PartTwo.Three.dataOfSetup hS S).sig →
        CFSG.Open.pRank 7 (PartTwo.Three.dataOfSetup hS S).M ≤ 2 := fun h7σ =>
      Nat.le_of_not_lt fun h73 => h7σ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC
        S.witness.maxLocal (by norm_num) le_rfl h73)
    have h17J := s21_17RJ1_of_three _ _ h211 h5 hn3 h6 hSg h8107 h920J1 h7
    have h846 := PartTwo.Three.r846_dataOfSetup hGy.griess hSE5 hSE3 hS hUC hC hGy.k36 S
    have h847T := r847E3Thin_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      hGy.cyclicSylowThreeOutAbelian hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S
    have h847S := r847E3SU3_dataOfSetup_of_dvd hSE5 hSEZ hG3 CFSG.AGLEmbedding.kFactReeInvolution
      hSE3 hGy.griess uc22pwCartanSU3_holds uc22pwTorusSU3_holds hS S h846
      (r847E3Dvd_dataOfSetup hSE5 hSEZ hGy.griess hS S)
    have h212 := s21_12_of_s21_12R3 h5 hSg h847T h3
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput PartTwo.thinList13_holds
      PartTwo.Inputs1719.k_LieModelNotL2_holds h70.s21_12R3
    have h16 : S21_16 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_16_of_s21_6Inf h6 h212 (s21_13_of h3 h5 hn3) h70.s21_14
        CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
    have h17 : S21_17 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
      s21_17_of_residualT hS.rank hGy.griess h211
        (PartTwo.Three.s21_17R_one_pow_of_three hS.rank hGy.griess _ _) hSg
        (conclusion76_of_r76Sig h76) h16 h15T (s21_normalSp4_of _ _ hSg h211)
        (s21_17RT_of_s21_17RT2 h212 h70.r8_69N hn3
          (s21_17RT2_of_s21_17RJ1 hS.rank hSE3 h70.r8_2 hn3 h17J))
    have h18 := s21_18_of _ _ h17 hGe.toGlobal22d.toGlobal22b.schreier
    have h2119 := s21_19_of_r847E3Thin _ _ h211 h212 h8107 h847T hS.rank h920odd hSg.nonempty hn3
    have h219 := s21_9Sig3_dataOfSetup_of_r847E3SU3 hGy.griess hSE5 hSE3 hS hUC hC S h211 h846 h847S
    have h78 := PartTwo.Three.r7_8R3p3_dataOfSetup hG3 CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS
      hUC hC S
    exact h70.toSteps67Three h212 h17J
      (s21_21TB_of_s21_21B (s21_21B_three_of_r847E3 hSE5 PartTwo.thinList13_holds
        hGy.cyclicSylowThreeOutAbelian hS hUC S h78 h70.r8_2 h846 h847T h847S h211 h16 h18 h2119
        h219))
      h219

  have steps66 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps66Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    intro S hMS
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
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB
      RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small
        RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
        PartOne.Section7.KIB3Small_holds)
    have h61 := steps67 S hMS
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h61.r8_2 h61.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK108 h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have hn3 := uc22p20g_hn3_of hGy.excFacts (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) h207
    have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    exact h61.toSteps66Three
      (s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S h61.r8_2
        (s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S))) hn3 (F10.k105Spor_of_rest hK)
      hrank hout

  have steps65 : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps65Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
    intro S hMS
    have hK : F10.K108H207 := F10.k108H207_holds
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
    have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB
      RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small
        RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
        PartOne.Section7.KIB3Small_holds)
    have h61 := steps66 S hMS
    have hSg := UC6S846.sigmaStd_dataOfSetup hS S
    have h76 := PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S
    have hr66 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
    have h201 := s20_1_124 (PartTwo.Three.dataOfSetup hS S) hr66 hGh.listB_nonabelian
    have h204 := uc22m22_s20_4 (PartTwo.Three.dataOfSetup hS S) hGe hr66
    have h206 := PartTwo.Three.s20_6_dataOfSetup_of_r880J4 hK331 hS S hSg h76 h61.r8_2 h61.r8_80J4
    have h207 : S20_7 (PartTwo.Three.dataOfSetup hS S) :=
      uc22p20q_s20_7_of hF22f hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 := uc22p22r_s21_1_of_k108H207 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)
      hK h201 h204 h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have hn3 := uc22p20g_hn3_of hGy.excFacts (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) h207
    have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    exact h61.toSteps65Three
      (s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S h61.r8_2
        (s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S))) hn3

  exact notTIStage1930_of_steps65Three hS hC steps65 hUC

end Three

end CFSG.LocalAnalysis.UniquenessCase.UC22
