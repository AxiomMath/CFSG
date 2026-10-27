module

public import CFSG.RankThree.GF2n.Stroth80.Unconditional
public import CFSG.RankThree.GF2n.Stroth80.Sec51Of34

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem stroth310RootStatement_unconditional : Stroth310RootStatement :=
  stroth310Root_of_34 stroth34Statement_unconditional

theorem stroth311bCardStatement_unconditional : Stroth311bCardStatement :=
  stroth311bCard_of_34 stroth34Statement_unconditional stroth310Statement_unconditional

theorem stroth311bCommStatement_unconditional : Stroth311bCommStatement :=
  stroth311bComm_of_34 stroth34Statement_unconditional stroth310Statement_unconditional
    stroth311aStatement_unconditional

theorem stroth51Statement_unconditional : Stroth51Statement :=
  stroth51_of_34 stroth34Statement_unconditional stroth310Statement_unconditional
    stroth311aStatement_unconditional

theorem sec8AExistsStatement_unconditional : Sec8AExistsStatement :=
  sec8AExists_of_34 stroth34Statement_unconditional stroth310Statement_unconditional
    stroth311aStatement_unconditional

theorem sec7AExistsStatement_unconditional : Sec7AExistsStatement :=
  sec7AExists_of_34 stroth34Statement_unconditional stroth310Statement_unconditional
    stroth311aStatement_unconditional

theorem sec5NatPointsSpStatement_unconditional : Sec5NatPointsSpStatement :=
  sec5NatPointsSp_of_34 stroth34Statement_unconditional

theorem sec5NatPointsOmegaStatement_unconditional : Sec5NatPointsOmegaStatement :=
  sec5NatPointsOmega_of_34 stroth34Statement_unconditional

end Certs

end CFSG.RankThree.GF2n.Stroth80
