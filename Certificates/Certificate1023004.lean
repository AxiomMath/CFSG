module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovPerm.M24Glue

public section

namespace Certificates

theorem certificate1023004 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Blueprint.NativeSporadic.M24 :=
  CFSG.KD.SporCovPerm.M24.sporKRestCover_three

end Certificates
