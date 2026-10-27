module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.LyThree.Facts

public section

namespace Certificates

theorem certificate1023017 :     CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.Ly :=
  CertificateChecks.KernelLyThree.cover_native

end Certificates
