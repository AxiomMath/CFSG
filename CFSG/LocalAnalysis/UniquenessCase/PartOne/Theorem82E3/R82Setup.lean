module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ExitsAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Std82E3Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Three
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36EqlStarCat
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs
public import Certificates.Certificate9726
public import Certificates.Certificate17430
public import Certificates.Certificate431004
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.LargeExtraspecial.AS35CS63E
public import CFSG.LargeExtraspecial.AS35CS63F
public import CFSG.LargeExtraspecial.AS35CS63J2
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Exc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefExceptional
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefPsp4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.OuterInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporCo1
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporHN
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporLy
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623c
public import CFSG.LocalAnalysis.UniquenessCase.UC6C634c
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRee
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C5
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Milestones.ASVolI.F431.Final4
public import CFSG.Quasithin.Vol2.Ch10SecALiftCore
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Comp2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LieData
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Trans
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.Timmesfeld.CorollaryBOutcome
public import Certificates.Certificate13501

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedThree_of_KIB StronglyEmbeddedThreeKIB_of_small KIB3Small_holds)

section


theorem r82_dataOfSetup_of_exits
    (hGF : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause) (hON : ONanExcludedSetup)
    (hL62 : L62ExcludedSetup) (h812 : Case812Setup) {G : Type} [Group G] [Finite G]
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (hMS : S.InMSigma) : UC22.F08.R82 (PartTwo.Three.dataOfSetup hS S) :=
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 := StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (StronglyEmbeddedThreeKIB_of_small hG3 KIB3Small_holds)
  r82_of_isEmpty
    (std82E3_dataOfSetup hS S hMS (UC6G.theoremCAt_dataOfSetup hS hUC hC S)
      (UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
          (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
              UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds)
          UCK.l34OuterFree) S)
      (PartTwo.Three.r76Sig_dataOfSetup Section7.SEFive.stronglyEmbeddedFive_holds hSE3 hS S))
    (Ctx82E3.false_dataOfSetup_of_exits hGF hON hL62 h812 hS hUC hC S hMS)

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
