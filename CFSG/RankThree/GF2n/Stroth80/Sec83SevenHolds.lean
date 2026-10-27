module

public import CFSG.RankThree.GF2n.Stroth80.Sec53FinalAssembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

section Certs

theorem stroth53Statement_unconditional : Stroth53Statement :=
  stroth53Statement_holds stroth34Statement_unconditional stroth310RootStatement_unconditional
    stroth51Statement_unconditional

end Certs

end CFSG.RankThree.GF2n.Stroth80
