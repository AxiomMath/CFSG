module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Fi23.Setup
import Certificates.Kernel.Fi23Cov.GlueThree
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace Certificates

theorem certificate1023009 :     CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.Fi23.J :=
  CFSG.KD.Fi23Cov.sporKRestCover_three_J

end Certificates
