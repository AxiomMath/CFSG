module

public import CFSG.RankThree.GF2n.AssemblyFour
public import CFSG.GF2Type.Smith1979CharTwoKPHolds

public section

namespace CFSG.RankThree.GF2n

section Five


theorem gf2nType_of_tim81_stroth_smith
    (hTim81 : Tim81UnitaryStatement)
    (hStroth : Stroth80.Stroth1980Statement) (hSmith : Smith81.Smith1981Statement) :
    GF2nTypeStatement :=
  gf2nType_of_stroth_smith CFSG.GF2Type.smith1979CharTwoKP_holds hTim81 hStroth hSmith

end Five

end CFSG.RankThree.GF2n
