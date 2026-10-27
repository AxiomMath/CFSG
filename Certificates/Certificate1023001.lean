module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovPerm.M12Glue

public section

namespace Certificates

theorem certificate1023001 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Blueprint.NativeSporadic.M12 :=
  CFSG.KD.SporCovPerm.M12.sporKRestCover_three

end Certificates
