module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovPerm.M23Glue

public section

namespace Certificates

theorem certificate1023003 :     CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Blueprint.NativeSporadic.M23 :=
  CFSG.KD.SporCovPerm.M23.sporKRestCover_three

end Certificates
