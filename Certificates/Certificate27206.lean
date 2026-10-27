module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24TriData
import Certificates.Kernel.G24Tri.C27206

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.G24Aut in
theorem certificate27206 : trianglesOK = true :=
  KernelG24.Tri27206.triangles_ok

end Certificates
