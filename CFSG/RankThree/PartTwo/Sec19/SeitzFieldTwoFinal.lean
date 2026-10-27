module

public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoAssembly
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8

public section

namespace CFSG.RankThree.PartTwo.Sec19

theorem u38FieldPlaneGen_holds : U38FieldPlaneGen := by
  unfold U38FieldPlaneGen
  intro K _ h E hE hc hN
  exact planeGen_unitaryPSU_eight h hE hc hN

theorem seitzThreeLThreePiField_holds :
    SeitzThreeLThreePiField :=
  seitzThreeLThreePiField_of_u38 u38FieldPlaneGen_holds

theorem seitzThreeLThreePiFieldTwo_holds :
    SeitzThreeLThreePiFieldTwo :=
  seitzThreeLThreePiFieldTwo_of_u38 u38FieldPlaneGen_holds

end CFSG.RankThree.PartTwo.Sec19
