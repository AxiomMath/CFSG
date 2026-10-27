module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.LieType.BorelTits.RadicalLinear.Stated

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem radicalTwoSubgroupLinearStatement_holds : RadicalTwoSubgroupLinearStatement :=
  fun r K _ _ _ hK U hU _ hrad =>
    CFSG.LieType.BorelTits.RadicalLinear.radicalTwoSubgroup_statedProj r K hK U hU hrad

end CFSG.RankThree.GF2n.Stroth80
