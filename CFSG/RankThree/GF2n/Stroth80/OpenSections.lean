module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClSiegel
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClMcLaughlinProof
public import CFSG.RankThree.GF2n.Stroth80.Sec34ClassicalProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem stroth310Statement_unconditional : Stroth310Statement :=
  stroth310_of_mcLaughlin stroth34Statement_unconditional mcLaughlinStatement_holds

end Certs

end CFSG.RankThree.GF2n.Stroth80
