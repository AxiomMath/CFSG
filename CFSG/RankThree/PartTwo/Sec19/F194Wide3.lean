module

public import CFSG.RankThree.PartTwo.Sec19.LitScopeProof
public import CFSG.RankThree.PartTwo.Sec19.Census194.Dispatch
public import CFSG.RankThree.PartTwo.Sec19.Census194.AltTen
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194RankOne
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psl
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psu
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Sp
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Omega
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194G2
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Small
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FrontierThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.FinalOfTypeBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBFinal
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusCent
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Corner

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.HardMathSupport.Cooperstein



theorem asc81bNineThreeNat_holds
    : Asc81bNineThreeNat :=
  Coordinator.asc81bNineThreeNat_of_three
    (Coordinator.TwE6.coopersteinNoIrrFFTwistedE6_of_typeBound
      fun _ hf K _ _ _ hK σ hσ => Coordinator.TwE6.twTypeBoundStmt_proved hf K hK σ hσ)
    StructureLie.orthMinusCentOb_proved
    (AlternatingGeometry.e0NonShortNotHYcStatement_of_caseI
      AlternatingGeometry.E0Sub.e0NonShortNotCaseIStatement_holds)

theorem asc81bNineThreeNatRank_holds
    : Asc81bNineThreeNatRank :=
  asc81bNineThreeNatRank_of_nat asc81bNineThreeNat_holds

theorem item194UsedWide3_of_item316
    (h316 : Item316) : Item194UsedWide3 :=
  item194UsedWide3_of_natRank (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
    asc81bNineThreeNatRank_holds
    (CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
    h316 (ks194ClassicalCensus_of_nodes Census194.RonanC194.survPSL_holds
        Census194.RonanC194.survPSU_holds Census194.RonanC194.survPSp_holds
        Census194.RonanC194.survPOmegaPlus_holds Census194.RonanC194.survPOmegaMinus_holds
        Census194.RonanC194.idPSL_holds Census194.RonanC194.idPSU_holds
        Census194.RonanC194.idPSp_holds Census194.RonanC194.idPOmegaMinus_holds
        Census194.RonanC194.idG2_holds Census194.RonanC194.idSmall_holds
        Census194.RonanC194.rankOne_holds Census194.not_isClassicalTwoOrG2_alt_ten)

end CFSG.RankThree.PartTwo.Sec19
