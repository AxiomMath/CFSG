module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovPerm.M22Glue

public section

namespace Certificates

theorem certificate1023002 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Blueprint.NativeSporadic.M22 :=
  CFSG.KD.SporCovPerm.M22.sporKRestCover_three

end Certificates
