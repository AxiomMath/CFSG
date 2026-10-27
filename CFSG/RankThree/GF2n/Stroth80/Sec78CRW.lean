module

public import CFSG.RankThree.GF2n.Stroth80.Sec78CentreMpr
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsCRW

public section

namespace CFSG.RankThree.GF2n.Stroth80


theorem sec7CRW_of_inputs (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hSch : Sec7SchurStatement) : Sec7CRWStatement :=
  sec7CRW_of_centre h310chi hA (sec7CentreMpr_of_inputs h34 h51 h52a hA) hSch

theorem sec7Centre_of_inputs (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) : Sec7CentreStatement :=
  sec7Centre_of_mp_mpr (sec7CentreMp_of_inputs h51 h52a hA)
    (sec7CentreMpr_of_inputs h34 h51 h52a hA)

end CFSG.RankThree.GF2n.Stroth80
