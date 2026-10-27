module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.HS.Group
public import Certificates.Data.CFSGNative.Co3.Data
import Certificates.Kernel.SporCovF2.Co3ThreeGlue

public section

namespace Certificates

theorem certificate1023401 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3
      ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Co3.Native.co3Data) :=
  CFSG.KD.SporCovF2.Co3Three.sporKRestCover_three_J

end Certificates
