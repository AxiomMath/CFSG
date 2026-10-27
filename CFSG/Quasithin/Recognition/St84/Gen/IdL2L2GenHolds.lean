module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qIdentHolds
public import CFSG.Quasithin.Recognition.St84.Gen.St84LLOddAssembly

public section

namespace CFSG.Quasithin.F112R.St84

theorem idL2L2GenW_holds :
    IdL2L2GenW :=
  idL2L2GenW_of_odd st84LLOdd_holds

theorem idL2L2Gen_holds :
    IdL2L2Gen :=
  idL2L2GenW_holds.idL2L2Gen

end CFSG.Quasithin.F112R.St84

end
