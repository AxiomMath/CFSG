module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Suz.Setup
import Certificates.Kernel.SporCovBase.SuzThreeGlue

public section

namespace Certificates

theorem certificate1023204 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.Suz.J :=
  CFSG.KD.SporCovBase.SuzThree.sporKRestCover_three_J

end Certificates
