module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Fi24.Setup
import Certificates.Kernel.Sporadic.Fi24Ctl3.Glue

public section

namespace Certificates

theorem certificate1023011 : CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.Fi24.J :=
  CFSG.KD.Fi24Ctl3.sporKRestCover_three_J

end Certificates
