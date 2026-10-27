module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.ON.Setup
import Certificates.Kernel.SporCovBase.ONGlue

public section

namespace Certificates

theorem certificate1023206 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.ON.J ∧
      CFSG.StandardType.SporadicShape.SporKRestCover 7 ↥CFSG.Sporadic.ON.J :=
  ⟨CFSG.KD.SporCovBase.ON.sporKRestCover_three_J, CFSG.KD.SporCovBase.ON.sporKRestCover_seven_J⟩

end Certificates
