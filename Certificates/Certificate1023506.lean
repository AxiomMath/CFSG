module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Th.Setup
import Certificates.Kernel.ThThreeCov.Facts

public section

namespace Certificates

theorem certificate1023506 :     CFSG.StandardType.SporadicShape.SporKRestCover 3 ↥CFSG.Sporadic.Th.J :=
  CertificateChecks.KernelThThreeCov.cover1023506

end Certificates
