module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Final
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e7Final
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e6Final
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Final

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar LevTwoType

theorem excFinite_E8 :
    ExcFinite Tag.E8 kacE8 := levTwoS3b_e8_excFinite

theorem excFinite_E7 :
    ExcFinite Tag.E7 kacE7 := levTwoS3e7_excFinite

theorem excFinite_E6 :
    ExcFinite Tag.E6 kacE6 := levTwoS3e6_excFinite

theorem excFinite_F4 :
    ExcFinite Tag.F4 kacF4 := levTwoS3f4_excFinite

end CFSG.StandardType.LevTwo
