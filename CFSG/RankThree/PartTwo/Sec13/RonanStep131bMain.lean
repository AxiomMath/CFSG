module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bLevel1
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPieces
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12Piece
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL227
public import CFSG.RankThree.PartTwo.Sec4.RonanK423Items

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.TBLit (griessMultipliersAllModels_holds)

theorem step131bSLTwoInEUOdd_of_item131a_and_pieceM12
    (h131a : Item131a) (hM12 : PieceM12) : Step131bSLTwoInEUOdd :=
  step131bSLTwoInEUOdd_of_pieces struct_holds
    (level1_holds Sec4.rank3II_4_5
      (Sec4.Item41Narrow.item4_1LargePrime_of_griess griessMultipliersAllModels_holds)
      (KFacts.outFixCentralThreeAbelian46Rank_of_narrow41
        (Sec4.Item41Narrow.item4_1LargePrime_of_griess griessMultipliersAllModels_holds)
        (Sec4.Item41Narrow.item4_1ThreeCover_of_griess griessMultipliersAllModels_holds)
        (Sec4.Census.rank3II_4_3_of_griess_noItem41 griessMultipliersAllModels_holds))
      Sec4.rank3II_4_9 (Sec4.rank3II_4_7W_of (Sec4.Census.rank3II_4_6_of_griess_noItem41
          griessMultipliersAllModels_holds
          (Sec4.Census.coverCenterThreeRest_of griessMultipliersAllModels_holds))) Sec4.item4_23_holds
      Sec4.RonanStep462.step463Alt_holds)
    pieceA7M22_holds pieceHJ_holds pieceL3_holds (pieceL227_holds h131a) hM12

theorem step131bSLTwoInEUOdd_of_item131a
    (h131a : Item131a) : Step131bSLTwoInEUOdd :=
  step131bSLTwoInEUOdd_of_item131a_and_pieceM12 h131a (pieceM12_holds h131a Sec4.rank3II_4_5)

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
