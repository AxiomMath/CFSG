module

public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofObs

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

theorem step143HJCompOne_of_item4_25Fix (h425 : Sec4.Item4_25Fix) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement)
    (hR : Step143HJCompRank) (hM : Step143HJCompM24) : Step143HJCompOne :=
  step143HJCompOne_of h425 h41 hGW h134 h48 hR step143HJObs hM

end CFSG.RankThree.PartTwo.Sec14
