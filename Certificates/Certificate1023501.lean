module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.J4Cov3.Facts

public section

namespace Certificates

theorem certificate1023501 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.J4 :=
  CertificateChecks.KernelJ4Cov3.sporKRest_cover_J4_3_native

end Certificates
