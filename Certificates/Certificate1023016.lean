module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.HN1023016.Facts

public section

namespace Certificates

theorem certificate1023016 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 5 CFSG.Blueprint.NativeSporadic.HN :=
  CertificateChecks.KernelHN1023016.sporKRest_cover_HN_5_native

end Certificates
