module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneLie
import CFSG.RankThree.GF2n.Stroth80.Sec7TailRadicalG2
import CFSG.RankThree.GF2n.Stroth80.Sec7TailRadicalD4

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem radicalTwoSubgroupRankTwoStatement_holds : RadicalTwoSubgroupRankTwoStatement :=
  fun X _ _ hX => hX.elim (radicalTwoSubgroup_g2 X) (radicalTwoSubgroup_trialityD4 X)

end CFSG.RankThree.GF2n.Stroth80

end
