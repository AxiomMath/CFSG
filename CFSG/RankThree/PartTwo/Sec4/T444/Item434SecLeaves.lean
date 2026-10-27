module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeAssembly
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG23
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofRee
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM22
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM23Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM24Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenJ2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenHS
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHeNine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRuNine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_9Cover
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL9Cover
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporONan
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_27
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLy27
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuz27
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo327
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo227
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHN27
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporTh27

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.LieType.SeitzGeneration

section Leaves


theorem item4_34Sec_of_leaves (hT : SeitzThreeTrialityWideTwo)
    (hA : SeitzExcAnisotropicTrialityThreeTwo) (h27R : Seitz434RestTwentySeven)
    (h27O : Seitz434OtherTwentySeven) : Item4_34Sec :=
  item4_34Sec_of (seitz434_of_seitzFieldTwo hT hA h27R)
    (Item41Narrow.item434LayerRanks_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
    (item434CharThree_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      item434CharThreeG2 item434CharThreeL4 item434CharThreeU4 item434CharThreeRee)
    (item434SmallTwo_of_leaves hT hA h27O) item434Alt
    (item434Spor_of_remainder item434Spor_M12_9 item434Spor_M22_9 item434Spor_M23_9
      item434Spor_M24_9 item434Spor_J2_9 item434Spor_HS_9 item434Spor_J4_9 item434Spor_He_9
      item434Spor_Ru_9 item434Spor_J3_9Cover item434Spor_McL_9Cover item434Spor_ONan_9Cover
      item434Spor_J3_27 item434Spor_McL_27 item434Spor_Ly_27 item434Spor_Suz_27
      item434Spor_Co3_27 item434Spor_Co2_27 item434Spor_HN_27 item434Spor_Th_27)

end Leaves

end CFSG.RankThree.PartTwo.Sec4
