module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Classical
public import CFSG.RankThree.GF2n.Stroth80.Sec34InputsProof
public import CFSG.RankThree.GF2n.Stroth80.Sec37InputsProof
public import CFSG.RankThree.GF2n.Stroth80.Sec37HKSProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem stroth34Statement_unconditional : Stroth34Statement :=
  stroth34Statement_of_classical hksStatement_holds sl2ModuleDimStatement_holds

theorem stroth37Statement_unconditional : Stroth37Statement :=
  stroth37Statement_of_classical hksNormal_holds sl2ModuleDimStatement_holds
    sl2FixedLineDimStatement_holds

end Certs

end CFSG.RankThree.GF2n.Stroth80
