module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PMain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3P149Three
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aE3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112E3NN
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KThin
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
public import CFSG.RankThree.PartTwo.Sec11.Item116R2K1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds


public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]


theorem s21_12_dataOfSetup_of_l3PTwo_f2 (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G)
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h207 : S20_7 (PartTwo.Three.dataOfSetup hS S))
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h3 : S21_3 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (hL3PTwo : S21_12aFR34L3PTwo (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S)))
    (hF2 : S21_12aFR34F2 (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S))) (Ch : Choice2011 G) :
    S21_12 (PartTwo.Three.dataOfSetup hS S) Ch := by
  suffices h : S21_12 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) from
    fun h1930 c => h h1930 (c.mono (fun _ _ _ => trivial))
  have hgr := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hSEZ := PartOne.Section7.stronglyEmbeddedFiveZ_holds
  have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
    PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
      UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have hn3 := uc22p20g_hn3_of uc22p20g_excFacts _ (fun _ _ => True) h207
  have h5 := s21_5_dataOfSetup hSQ hSE5 hSE3 KBridge.kThinSimple_holds hS S h82
    (s21_15Two_of_certificate113 _ _ h211 hSg (uc22r899e3_dataOfSetup hS hUC S))
  have hKF7 := kf7Use_dataOfSetup hSQ hSE5 hSE3 hS S
  have hL3P : S21_12aFR34L3P (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S)) :=
    s21_12aFR34L3P_of_res_two
      (fun h1930 c => hn3 h1930 (c.mono (fun _ _ _ => trivial)))
      (uc22s2112l3p_of_inputs hgr hSg hKF7
        (fun h1930 c => h5 h1930 (c.mono (fun _ _ _ => trivial)))
        (r149L3P_dataOfSetup hS hUC hC S)) hL3PTwo
  have hR34 := s21_12aFR34_of_rest hgr h82 h211 (fun _ _ _ => trivial)
    (s21_12aFR34L3_dataOfSetup_of_l3P hS S hL3P) hF2
    (s21_12aFR34F3_dataOfSetup hS S)
  have h12R3 := s21_12R3_dataOfSetup_of_s21_12aF hSQ hSE5 hSEZ hSE3 KBridge.kThinSimple_holds
    PartTwo.thinList13_holds hS hUC S h82 h211
    (s21_12aF_dataOfSetup_of_s21_12aFR34 hSQ hSE5 hSE3 KBridge.kThinSimple_holds uc22p20g_excFacts
      listBNonabelian CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      PartTwo.thinList13_holds PartTwo.Inputs1719.k_LieModelNotL2_holds hgr hS hUC hC S
      h207 h211 h3 h82 h614 hR34)
  exact s21_12_of_s21_12R3 h5 hSg
    (r847E3Thin_dataOfSetup hSE5 hSEZ PartTwo.thinList13_holds
      CFSG.RankThree.PartTwo.Sec11.cyclicSylowThreeOutAbelian_holds hG3
      CFSG.AGLEmbedding.kFactReeInvolution hSE3 hS S)
    h3 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput PartTwo.thinList13_holds
    PartTwo.Inputs1719.k_LieModelNotL2_holds h12R3

end CFSG.LocalAnalysis.UniquenessCase.UC22
