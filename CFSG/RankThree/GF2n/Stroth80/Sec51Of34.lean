module

public import CFSG.RankThree.GF2n.Stroth80.Sec311bCard
public import CFSG.RankThree.GF2n.Stroth80.Sec311bComm
public import CFSG.RankThree.GF2n.Stroth80.Sec51Main
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaConsumers
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth51_of_34 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h311a : Stroth311aStatement) : Stroth51Statement :=
  stroth51_of_inputs h34 (stroth310Root_of_34 h34) h311a (stroth311bComm_of_34 h34 h310 h311a)
    (stroth311bCard_of_34 h34 h310)

theorem sec5NatPointsSp_of_34 (h34 : Stroth34Statement) : Sec5NatPointsSpStatement :=
  sec5NatPointsSp_of h34 (stroth310Root_of_34 h34)

theorem sec5NatPointsOmega_of_34 (h34 : Stroth34Statement) : Sec5NatPointsOmegaStatement :=
  sec5NatPointsOmega_of h34 (stroth310Root_of_34 h34)

theorem sec8AExists_of_34 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h311a : Stroth311aStatement) : Sec8AExistsStatement :=
  sec8AExists_of h34 (stroth310Root_of_34 h34) (stroth51_of_34 h34 h310 h311a)

theorem sec7AExists_of_34 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h311a : Stroth311aStatement) : Sec7AExistsStatement :=
  sec7AExists_of h34 (stroth310Root_of_34 h34) (stroth51_of_34 h34 h310 h311a)

end CFSG.RankThree.GF2n.Stroth80
