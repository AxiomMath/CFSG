module

public import CFSG.RankThree.PartTwo.Sec4.Item463Proof
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowKFacts
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowLargePrime
import CFSG.RankThree.PartTwo.Sec4.Item462AltProof
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKLTwo
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofNoFieldKind
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo
import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanStep462

theorem step462Alt_holds
    : Step462Alt :=
  Item462AltProof.step462Alt_of Item462AltProof.kLTwoCentralizer_holds kChevTwoCentralizer_holds
    Item462AltProof.KSLThree.kSLThreeCentralizerQ_holds Item462AltProof.ksLThreeNoFieldKind_holds

theorem step463Alt_holds
    : Step463Alt :=
  Item462AltProof.step463Alt_of
    (Item41Narrow.item4_1LargePrime_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
    Item462AltProof.kLTwoCentralizer_holds kChevTwoCentralizer_holds
    Item462AltProof.KSLThree.kSLThreeCentralizerQ_holds

theorem item4_62_of_noAlt
    (h45 : Item4_5) (h41 : Item4_1LargePrime) (hKF : KFacts.OutFixCentralThreeAbelian46Rank)
    (h49 : Item4_9) (h47 : Item4_7W) (h423 : Item4_23) (hUα : Step462UAlpha) : Item4_62 :=
  item4_62_of h45 h41 hKF h49 h47 h423 step462Alt_holds hUα

theorem item463Inv_of_items_noAlt
    (h45 : Item4_5) (h41 : Item4_1LargePrime) (h41c : Item4_1ThreeCover) (h43 : Item4_3)
    (h49 : Item4_9) (h47 : Item4_7W) (h423 : Item4_23) : Sec10.Item463Inv :=
  item463Inv_of h45 h41 (KFacts.outFixCentralThreeAbelian46Rank_of_narrow41 h41 h41c h43) h49 h47
    h423 step463Alt_holds

end CFSG.RankThree.PartTwo.Sec4.RonanStep462

end
