module

public import CFSG.RankThree.GF2n.Stroth80.Sec52bProof
public import CFSG.RankThree.GF2n.Stroth80.Sec78Zt
public import CFSG.RankThree.GF2n.Stroth80.Sec56Singular
public import CFSG.RankThree.GF2n.Stroth80.Sec7NOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSchur
public import CFSG.RankThree.GF2n.Stroth80.Sec712
public import CFSG.RankThree.GF2n.Stroth80.Stroth711Strong
public import CFSG.RankThree.GF2n.Stroth80.Sec78CRW

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem sec7CentreStatement_holds : Sec7CentreStatement :=
  sec7Centre_of_inputs stroth34Statement_unconditional stroth51Statement_unconditional
    stroth52aStatement_holds sec7AExistsStatement_unconditional

theorem sec7ZCardStatement_holds : Sec7ZCardStatement :=
  sec7ZCard_of_inputs stroth51Statement_unconditional sec7AExistsStatement_unconditional

theorem sec7CentreMpStatement_holds : Sec7CentreMpStatement :=
  sec7CentreMp_of_inputs stroth51Statement_unconditional stroth52aStatement_holds
    sec7AExistsStatement_unconditional

theorem sec7ZtStatement_holds : Sec7ZtStatement :=
  sec7Zt_of_inputs stroth34Statement_unconditional stroth310Statement_unconditional
    stroth51Statement_unconditional stroth52aStatement_holds sec7AExistsStatement_unconditional
    sec8AExistsStatement_unconditional (stroth56Nat_of_34 stroth34Statement_unconditional)
    sec5NatPointsOmegaStatement_unconditional sec5NatPointsSpStatement_unconditional

theorem sec7CVStatement_holds : Sec7CVStatement :=
  sec7CV_of_inputs stroth34Statement_unconditional
    (stroth310Root_of_34 stroth34Statement_unconditional)
    sec7AExistsStatement_unconditional stroth52bStatement_holds

theorem sec7VtIrredStatement_holds : Sec7VtIrredStatement := sec7VtIrred_holds

theorem sec7NOrderStatement_holds : Sec7NOrderStatement :=
  sec7NOrder_of stroth34Statement_unconditional stroth51Statement_unconditional
    sec7AExistsStatement_unconditional sec5NatPointsOmegaStatement_unconditional

theorem sec7ZVStatement_holds : Sec7ZVStatement :=
  sec7ZV_of_parts sec7ZtStatement_holds sec7CentreMpStatement_holds
    (stroth310Chi_of_34 stroth34Statement_unconditional)

theorem sec7SchurStatement_holds : Sec7SchurStatement :=
  sec7Schur_of_parts stroth34Statement_unconditional
    (stroth310Chi_of_34 stroth34Statement_unconditional) sec7CentreMpStatement_holds
    sec7ZVStatement_holds sec7ZCardStatement_holds

theorem sec7CRWStatement_holds : Sec7CRWStatement :=
  sec7CRW_of_inputs stroth34Statement_unconditional
    (stroth310Chi_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional
    stroth52aStatement_holds sec7AExistsStatement_unconditional sec7SchurStatement_holds

theorem stroth711StrongStatement_holds : Stroth711StrongStatement :=
  stroth711Strong_holds stroth34Statement_unconditional
    (stroth310Root_of_34 stroth34Statement_unconditional) stroth52aStatement_holds
    sec7NOrderStatement_holds sec7AExistsStatement_unconditional

theorem stroth712Statement_holds : Stroth712Statement :=
  stroth712_holds stroth34Statement_unconditional stroth51Statement_unconditional
    sec7AExistsStatement_unconditional sec7ZtStatement_holds sec7ZCardStatement_holds

end Certs

end CFSG.RankThree.GF2n.Stroth80
