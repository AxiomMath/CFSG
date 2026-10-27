module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps87
public import Certificates.Certificate291400
public import CFSG.LocalAnalysis.UniquenessCase.UC22Setup4S21Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22Q35NormSylowAlphaHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22Q35PermFiveHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LFFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LTFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LK2Core
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwoFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2SigFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35Four
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3F
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LHead
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PMain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Alpha
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.UniquenessCase.UCK35wHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusU7
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35
public import Certificates.Certificate9726
public import Certificates.Certificate17430
public import Certificates.Certificate431004

public import Certificates.Certificate8058
public import Certificates.Certificate8059
public import Certificates.Certificate9542
public import Certificates.Certificate9543
public import Certificates.Certificate12610
public import Certificates.Certificate12612
public import Certificates.Certificate12613
public import Certificates.Certificate12614
public import Certificates.Certificate12623
public import Certificates.Certificate12635
public import Certificates.Certificate12636
public import Certificates.Certificate12641
public import Certificates.Certificate428001
public import Certificates.Certificate428004
public import Certificates.Certificate12611
public import Certificates.Certificate12617
public import Certificates.Certificate12618
public import Certificates.Certificate12619
public import Certificates.Certificate12620
public import Certificates.Certificate12634
public import Certificates.Certificate12637
public import Certificates.Certificate13513
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate24945
public import Certificates.Certificate24946

public import Certificates.Certificate7252

public import Certificates.Certificate1322003
public import Certificates.Certificate1322004
public import Certificates.Certificate1322005
public import Certificates.Certificate1322006
public import Certificates.Certificate1322007
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallSylow
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Root
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CentData
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Res
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Proof
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XE
public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps73
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsS
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjKer
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutFix
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)


theorem steps87_dataOfSetup4_of_q35
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (hQ35 : S21_12aFR34F2Q35 (UC6.dataOfSetup4 hS hU S)
      (Choice214U (UC6.dataOfSetup4 hS hU S))) :
    Steps87 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  have hgr := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hK3 : StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hRest := s21_3Rest15_dataOfSetup4 hS hU S hMS hPart
  have hs := setup4S21Facts_dataOfSetup4 hS hU S hMS hPart hRest
  have hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → True :=
    fun _ _ _ => trivial
  refine {
    s21_3Rest15 := hRest
    s21_14R4F := s21_14R4F_dataOfSetup4 hS hU S hMS hPart
    s21_14R3UF := s21_14R3UF_dataOfSetup4 hgr hSE hK3 hB3 hS hU S hMS hPart
    s21_14R3L := s21_14R3L_setup4_of_residuals hgr hS hU S hPart (fun _ _ => True)
      hs.r76 hs.hn3 hs.s21_3 hs.s21_5
      (s21_14R3LF_dataOfSetup4 hS hU S hMS hPart)
      (s21_14R3LT_dataOfSetup4 hS hU S hMS hPart)
      (s21_14R3LK2_core hS hU S hMS hPart)
    s21_12aR34L3P := s21_12aFR34L3P_of_res_two
      (fun hH c => hs.hn3 hH (c.mono hCh))
      (uc22s2112l3p_setup4 hgr UCK.k35w_holds PartOne.Section8.stronglyEmbeddedCentralFree_holds
        hS hU S hMS hPart hSE hK3 hB3
        CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds hs.kf7
        (fun hH c => hs.s21_5 hH (c.mono hCh)))
      (s21_12aFR34L3PTwo_dataOfSetup4 hS hU S hMS hPart)
    s21_12aR34L3E := s21_12aFR34L3E_of_l3E2 kFieldAutOdd_holds kFunSplit_holds hgr
      (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hs.kf7 hs.hn3 hs.s21_5 hs.r82 hs.s21_1 hCh
      (s21_12aFR34L3E2_dataOfSetup4 hS hU S hMS hPart)
    s21_12aR34F2Q35 := hQ35
    s21_12aR34F2Sig := s21_12aFR34F2Sig_dataOfSetup4 hS hU S hMS hPart
    s21_12aR34F2Even := s21_12aFR34F2Even_of_f2Even2 kFieldAutOdd_holds kFunSplit_holds
      kFunCount_holds hgr (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hs.kf7 hs.hn3 hs.s21_5
      hs.r82 hs.s21_1 hCh (s21_12aFR34F2Even2_dataOfSetup4 hS hU S hMS hPart)
    s21_12aR34F3Q35 := s21_12aFR34F3Q35_dataOfSetup4 hS hU S hMS hPart }


theorem steps87_dataOfSetup4
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    Steps87 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  have hs := setup4S21Facts_dataOfSetup4 hS hU S hMS hPart
    (s21_3Rest15_dataOfSetup4 hS hU S hMS hPart)
  exact steps87_dataOfSetup4_of_q35 hS hU S hMS hPart
    (s21_12aFR34F2Q35_of_kfacts kFieldAutOdd_holds kq35NormSylowAlpha_holds kQ35PermFive_holds
      (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hs.hn3 hs.s21_5 (fun _ _ _ => trivial))

end CFSG.LocalAnalysis.UniquenessCase.UC22
