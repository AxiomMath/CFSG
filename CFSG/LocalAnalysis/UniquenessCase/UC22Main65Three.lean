module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main64Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251n
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R77EqThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.S206ThreeJ4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.S2117PowThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsSixteen
import CFSG.LocalAnalysis.UniquenessCase.UC22K108HCore
import CFSG.LocalAnalysis.UniquenessCase.UC22K108Holds
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Holds
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Residue
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251m
import CFSG.LocalAnalysis.UniquenessCase.UC22S217Sp4
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899E3
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rTorus
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps65Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_6Inf : S21_6Inf D Ch
  s21_13 : S21_13 D Ch
  s21_14 : S21_14 D Ch
  s21_8 : S21_8Sp4 D Ch
  s21_21TB : S21_21TB D Ch
  s22_5_1R3 : S22_5_1R3 D Ch
  s21_12 : S21_12 D Ch
  s21_17RJ1 : S21_17RJ1 D Ch
  r8_2 : F08.R82 D
  r8_69N : F08.R869N D
  r8_69M : F08.R869MCons D
  r8_80J4 : F08.R880J4 D
  s21_22R3 : S21_22R3 D Ch
  s21_9Sig3 : S21_9Sig3 D Ch
  s22_fin3R : S22Fin3R D Ch

end Reduction

section Three

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem notTIStage1930_of_steps65Three
    (hS : RankThreeUC.Standing G)
    (hC : RankThreeUC.AGL81TheoremC G)
    (h : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps65Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) :
    RankThreeUC.NotTIStage1930 G := by
  intro hUC
  refine notTIStage1930_of_steps64Three hS hC (fun S hMS => ?_) hUC
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
  have h61 := h S hMS
  have hs := Standing22.ofSetup hS hUC hC hGy.k36 S hMS
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have h614 := UC6G.uc_theorem_6_14_three hS hUC hC hGy.k36 S
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
  have h16 : S21_16 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
    s21_16_of_s21_6Inf h61.s21_6Inf h61.s21_12 h61.s21_13 h61.s21_14
      CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
  have h17 : S21_17 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
    s21_17_of_residualT hS.rank hGy.griess h211
      (PartTwo.Three.s21_17R_one_pow_of_three hS.rank hGy.griess _ _) hSg
      (conclusion76_of_r76Sig h76) h16
      (s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S))
      (s21_normalSp4_of _ _ hSg h211)
      (s21_17RT_of_s21_17RT2 h61.s21_12 h61.r8_69N hn3
        (s21_17RT2_of_s21_17RJ1 hS.rank hSE3 h61.r8_2 hn3 h61.s21_17RJ1))
  have hid := uc22p22q_r613ident_of _ hs.sigma23 hs.r6_1 hs.sigma2
  have haut := uc22p22q_r613aut_of _ hs.sigma23 hs.r6_1 hs.sigma2 hs.cent
  have h119 : R119W (PartTwo.Three.dataOfSetup hS S) :=
    uc22p22u_r119W _ (uc22p22u_r118W PartTwo.thinList13_holds hGy.cyclicSylowThreeOutAbelian _
      (uc22p22u_c116W _ hSg hs.r6_1 hs.r6_3 (PartTwo.Three.r77Eq_dataOfSetup hSE5 hSE3 hS hUC S)
        (uc22p22q_r111_of _ hs.sigma23 hs.r6_1 hs.r6_11)
        (uc22p22q_r112_of _ hs.sigma23 hs.r6_1 hs.sigma2 hid hs.cent haut))
      (uc22p22u_c117W_of_R869MCons _ h61.r8_69M))
  have h31 : S22_3_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
    uc22p22p_s22_3_1_of _ _ (UC6.r6_40_2_holds hGy.u2 hGy.s25 _) fun _ c =>
      (uc22p22n_inCalV1_of_not_isTI _ hs.dataExt hs.r6_1 (uc22p22e_inCalV_U _) c.hU).2
  have h33 := uc22p22wj_s22_3_of_sp4 hGy.k148 _ _ hs.dataExt hs.r6_1 h31 h119 h16 h61.s21_8
  exact { h61 with
    s22_5_1 := s22_5_1_of_s22_5_1R3 hs.dataExt hs.r6_1 h119 h17 h31 h33.2 hSg h76 h614
      h61.s22_5_1R3 }

end Three

end CFSG.LocalAnalysis.UniquenessCase.UC22
