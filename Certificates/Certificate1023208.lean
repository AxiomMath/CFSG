module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.HS.Group
public import Certificates.Data.CFSGNative.Co2.Data
import Certificates.Kernel.SporCovF2.Co2FiveGlue

public section

namespace Certificates

theorem certificate1023208 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 5
      ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Co2.Native.co2Data) :=
  CFSG.KD.SporCovF2.Co2Five.sporKRestCover_five_J

end Certificates
