module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift

public section


namespace CFSG.StandardType.E6ThreeModel

theorem e6ThreeModel_holds : GGE6ThreeModelInput :=
  ⟨fun _ _ _ n hn hK h3 => e6ThreeModel_holds_E ggAbelianLift n hn hK h3,
    fun _ _ _ n hn hK h3 => e6ThreeModel_holds_T hn hK ggAbelianLift h3⟩

end CFSG.StandardType.E6ThreeModel
