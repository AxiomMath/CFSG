module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL62Exit
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsL62Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6aHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6bHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega8Minus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSp6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332THolds
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3


theorem l62ExcludedSetup_of_certificates : L62ExcludedSetup :=
  l62ExcludedSetup_of_inputs Theorem82.k6a_holds Theorem82.k6b_holds
      (Theorem82.k6c_of_facts
          ⟨Theorem82.SignedFacts.sp6K6cFacts_holds, Theorem82.SignedFacts.omega7K6cFacts_holds,
              Theorem82.SignedFacts.omega8MinusK6cFacts_holds,
              Theorem82.SignedFacts.slK6cFacts_holds 6, Theorem82.SignedFacts.suK6cFacts_holds 6,
              Theorem82.SignedFacts.slK6cFacts_holds 7, Theorem82.SignedFacts.suK6cFacts_holds 7⟩)
    UCK.k332ThreeAb_holds
    (Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
      UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4)
    Section7.SEFive.stronglyEmbeddedFive_holds
    (Section7.StronglyEmbeddedThree_of_KIB
      RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (Section7.StronglyEmbeddedThreeKIB_of_small
        RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
        Section7.KIB3Small_holds))
    (fun _ _ _ h => Theorem82.center_eq_bot_of_isLie811_of_ne h (by decide) (fun h => by cases h))
    k7L6TwoCentA_holds k7L6TwoPerfect_holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
