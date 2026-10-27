module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.He.Setup
import Certificates.Kernel.SporCovBase.HeGlue

public section

namespace Certificates

theorem certificate1023202 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.He.J ∧
      CFSG.StandardType.SporadicShape.SporKRestCover 5 ↥CFSG.Sporadic.He.J :=
  ⟨CFSG.KD.SporCovBase.He.sporKRestCover_three_J, CFSG.KD.SporCovBase.He.sporKRestCover_five_J⟩

end Certificates
