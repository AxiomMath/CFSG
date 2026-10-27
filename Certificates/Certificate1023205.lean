module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.He.Setup
import Certificates.Kernel.SporCovBase.HeGlue

public section

namespace Certificates

theorem certificate1023205 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 7 ↥CFSG.Sporadic.He.J :=
  CFSG.KD.SporCovBase.He.sporKRestCover_seven_J

end Certificates
