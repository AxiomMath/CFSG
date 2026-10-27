module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Suz.Setup
import Certificates.Kernel.SporCovBase.SuzGlue

public section

namespace Certificates

theorem certificate1023203 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 5 ↥CFSG.Sporadic.Suz.J :=
  CFSG.KD.SporCovBase.Suz.sporKRestCover_five_J

end Certificates
