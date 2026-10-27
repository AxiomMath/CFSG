module

public import CFSG.RankThree.GF2n.Stroth80.Sec51Unconditional
public import CFSG.RankThree.GF2n.Stroth80.Sec83SevenNoA
public import CFSG.RankThree.GF2n.Stroth80.Sec8AExistsProof
public import CFSG.RankThree.GF2n.Stroth80.Sec83Upper

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem stroth83_of_53_only' (h53 : Stroth53Statement) (h54 : Stroth54Statement)
    (hInv : Sec8InvStatement) (h82 : Stroth82Statement) (hC : Sec83UpperStatement) :
    Stroth83Statement :=
  stroth83_of_inputs stroth34Statement_unconditional stroth51Statement_unconditional h53 h54
      (sec5NatPointsSp_of_34 stroth34Statement_unconditional) sec8AExistsStatement_holds hInv h82 hC
      (sec83SevenStatement_of_minimal' stroth34Statement_unconditional h53
          (sec5NatPointsSp_of_34 stroth34Statement_unconditional))

theorem stroth83_of_53_only'' (h53 : Stroth53Statement) (h54 : Stroth54Statement)
    (h82 : Stroth82Statement) : Stroth83Statement :=
  stroth83_of_53_only' h53 h54 sec8InvStatement_holds h82
    (sec83Upper_of_53 stroth34Statement_unconditional h53 sec8AExistsStatement_holds
      (sec5NatPointsSp_of_34 stroth34Statement_unconditional))

end Certs

end CFSG.RankThree.GF2n.Stroth80
