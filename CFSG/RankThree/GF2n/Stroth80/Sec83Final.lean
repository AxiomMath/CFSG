module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Upper
public import CFSG.RankThree.GF2n.Stroth80.Sec83Seven
public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open


theorem stroth83_of_inputs_53 (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h54 : Stroth54Statement) (hPts : Sec5NatPointsSpStatement)
    (hA : Sec8AExistsStatement) (h82 : Stroth82Statement) : Stroth83Statement :=
  stroth83_of_inputs_inv h34 h51 h53 h54 hPts hA h82 (sec83Upper_of_53 h34 h53 hA hPts)
    (sec83Seven_of_53 h34 h53 hA hPts)

theorem stroth83_of_53 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h53 : Stroth53Statement) (h54 : Stroth54Statement)
    (h82 : Stroth82Statement) : Stroth83Statement :=
  stroth83_of_inputs_53 h34 h51 h53 h54 (sec5NatPointsSp_of h34 hRoot)
    (sec8AExists_of h34 hRoot h51) h82

end CFSG.RankThree.GF2n.Stroth80
