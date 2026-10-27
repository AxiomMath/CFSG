module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Fi22.Setup
import Certificates.Kernel.SporCovBase.Fi22Glue

public section

namespace Certificates

theorem certificate1023007 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.Fi22.J :=
  CFSG.KD.SporCovBase.Fi22.sporKRestCover_three_J

end Certificates
