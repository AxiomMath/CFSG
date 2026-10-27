module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.J2.Setup
import Certificates.Kernel.SporCovBase.J2Glue

public section

namespace Certificates

theorem certificate1023005 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.J2.J ∧
      CFSG.StandardType.SporadicShape.SporKRestCover 5 ↥CFSG.Sporadic.J2.J :=
  ⟨CFSG.KD.SporCovBase.J2.sporKRestCover_three_J, CFSG.KD.SporCovBase.J2.sporKRestCover_five_J⟩

end Certificates
