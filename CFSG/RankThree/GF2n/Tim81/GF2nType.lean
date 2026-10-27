module

public import CFSG.RankThree.GF2n.AssemblyFive
public import CFSG.RankThree.GF2n.Tim81.Main
public import CFSG.RankThree.GF2n.Tim81.RonanInputsHolds

public section

namespace CFSG.RankThree.GF2n.Tim81


theorem gf2nType_of_tim81_inputs
    (h79 : Tim79aStatementWCQ)
    (hStroth : Stroth80.Stroth1980Statement) (hSmith : Smith81.Smith1981Statement) :
    GF2nTypeStatement :=
  gf2nType_of_tim81_stroth_smith
    (tim81UnitaryStatement_of_inputs h79 CFSG.RankThree.PartOne.pushingUpCorollary_holds)
    hStroth hSmith

end CFSG.RankThree.GF2n.Tim81
