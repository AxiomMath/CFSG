module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Fi23.Setup
import Certificates.Kernel.Fi23Cov.GlueFive

public section

namespace Certificates

theorem certificate1023008 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 5 ↥CFSG.Sporadic.Fi23.J :=
  CFSG.KD.Fi23Cov.sporKRestCover_five_J

end Certificates
