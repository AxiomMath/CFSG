module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Fi24.Setup
import Certificates.Kernel.Sporadic.Fi24FiveK.Glue

public section

namespace Certificates

theorem certificate1023010 : CFSG.StandardType.SporadicShape.SporKRestCover 5 ↥CFSG.Sporadic.Fi24.J :=
  CFSG.KD.Fi24FiveK.sporKRestCover_J

end Certificates
