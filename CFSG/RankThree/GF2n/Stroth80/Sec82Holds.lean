module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Final
public import CFSG.RankThree.GF2n.Stroth80.Sec83SevenHolds
public import CFSG.RankThree.GF2n.Stroth80.Sec8Final
public import CFSG.RankThree.GF2n.Stroth80.Sec78CommWtSp
public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOmega
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Proved
public import CFSG.RankThree.GF2n.Stroth80.Sec54StatementFinal

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem sec8ZtStatement_holds : Sec8ZtStatement :=
  sec8Zt_of_inputs stroth34Statement_unconditional stroth51Statement_unconditional
    sec8AExistsStatement_unconditional
    (sec8CommWt_of_53 stroth34Statement_unconditional stroth53Statement_unconditional
      sec8AExistsStatement_unconditional
      (sec5NatPointsSp_of stroth34Statement_unconditional stroth310RootStatement_unconditional))
    stroth56Sp_holds

theorem stroth82Statement_holds : Stroth82Statement :=
  stroth82_of_inputs_final stroth34Statement_unconditional
    (stroth310Chi_of_34 stroth34Statement_unconditional) stroth310RootStatement_unconditional
    stroth311bCommStatement_unconditional stroth51Statement_unconditional
    stroth53Statement_unconditional sec8AExistsStatement_unconditional sec8ZtStatement_holds
    (close8Final_of_parts stroth34Statement_unconditional
      (stroth310Chi_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional
      sec8AExistsStatement_unconditional sec8ZtStatement_holds stroth311aStatement_unconditional
      stroth44Statement_unconditional stroth45Statement_unconditional stroth54Statement_holds
      stroth6NbarGeStatement_holds)

theorem stroth83Statement_holds : Stroth83Statement :=
  stroth83_of_53 stroth34Statement_unconditional stroth310RootStatement_unconditional
      stroth51Statement_unconditional stroth53Statement_unconditional stroth54Statement_holds
      stroth82Statement_holds

end Certs

end CFSG.RankThree.GF2n.Stroth80
