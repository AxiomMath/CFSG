module

public import CFSG.RankThree.GF2n.Stroth80.Sec51Of34
public import CFSG.RankThree.GF2n.Stroth80.Unconditional

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Certs

theorem sec8AExistsStatement_holds : Sec8AExistsStatement :=
  sec8AExists_of_34 stroth34Statement_unconditional stroth310Statement_unconditional
    stroth311aStatement_unconditional

end Certs

end CFSG.RankThree.GF2n.Stroth80
