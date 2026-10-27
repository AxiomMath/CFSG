module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6LB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe
public import CFSG.RankThree.GF2n.Stroth80.Sec51Unconditional

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem stroth6LBStatement_holds : Stroth6LBStatement :=
  stroth6LB_of_inputs stroth34Statement_unconditional stroth311aStatement_unconditional
    (stroth310Root_of_34 stroth34Statement_unconditional)

theorem stroth6SLDimStatement_holds : Stroth6SLDimStatement :=
  stroth6SLDim_of_34 stroth34Statement_unconditional

theorem stroth6NbarGeStatement_holds : Stroth6NbarGeStatement :=
  stroth6NbarGe_of_inputs stroth34Statement_unconditional stroth310Statement_unconditional
    (stroth310Root_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional

end Certs

end CFSG.RankThree.GF2n.Stroth80
