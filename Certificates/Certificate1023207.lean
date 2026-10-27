module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.HS.Group
public import Certificates.Data.CFSGNative.Co3.Data
import Certificates.Kernel.SporCovF2.Co3Glue

public section

namespace Certificates

theorem certificate1023207 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 5
      ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Co3.Native.co3Data) :=
  CFSG.KD.SporCovF2.Co3.sporKRestCover_five_J

end Certificates
