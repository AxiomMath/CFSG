module

public import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofD4
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec14

theorem item148S14_of_leaves
    (hN : Step148Normal) (hYBS : Step148YBShape) (hHJ : Step148HJ) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h429 : Step148Lift429) (hD4D : Step148D4Data) (hOne : Step148One) (hRank : Step148Rank)
    (hPGL : Step148PGL) : Item148S14 :=
  item148S14_of_steps hN (step148YB_of_shape hYBS) hHJ hCore hPoint hKT
    (step148Lift_of_lift429 h45 h48 h429) (step148D4_of_data hD4D) hOne hRank hPGL

end CFSG.RankThree.PartTwo.Sec14
