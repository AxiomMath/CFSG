module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovF2.HSGlue
public import Certificates.Data.CFSGNative.HS.Data

public section

namespace Certificates

theorem certificate1023101 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.HS := by
  intros
  exact @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv
    ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.HS.Native.hsData) CFSG.Blueprint.NativeSporadic.HS
    inferInstance inferInstance CFSG.Sporadic.Bridge.HS.nativeEquiv.symm 3
    CFSG.KD.SporCovF2.HS.sporKRestCover_three_J

end Certificates
