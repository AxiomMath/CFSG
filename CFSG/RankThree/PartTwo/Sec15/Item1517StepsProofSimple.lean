module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step1517Simple_of
    (h135 : Item135Simple) : Step1517Simple :=
  fun _ _ _ _ _ _ h _ hctx hno => ⟨Proof1517.isSimpleGroup_of_noY2 h135 h hctx hno,
    Proof1517.odd_card_inf_centralizer h hctx hno⟩

end CFSG.RankThree.PartTwo.Sec15
