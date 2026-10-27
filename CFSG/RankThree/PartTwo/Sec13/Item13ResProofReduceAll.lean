module

public import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCentral
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleTwoRank
import CFSG.RankThree.PartTwo.Sec13.KS135TwoRankCover
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofL3
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec13.Item13ResProofA7Z3

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Certificates


theorem item135Reduce_of_131a (h131a : Item131a) (h44 : Sec4.Item4_4) : Item135Reduce :=
  item135Reduce_of_items h131a h44
    (ks135TwoRank_of_cover ks135TwoRankCover Sec4.Sporadic.rank3II_4_14_local
      Sec4.Sporadic.rank3II_4_15)
    sporadicModels131

theorem rank3II_13_5_of_131a (h131a : Item131a) (h44 : Sec4.Item4_4)
    (hA7Z3 : Item135A7Z3HypT) (hA7 : Item135A7) : Item135 :=
  rank3II_13_5_of_steps (item135Reduce_of_131a h131a h44) (item135A7Z3_of hA7Z3) item135L3 hA7

end Certificates

end CFSG.RankThree.PartTwo.Sec13
