module

public import Certificates.Data.Fi24Rank.PlanesCheck
import Certificates.Kernel.LocalComp.Fi24Pl.A101705

public section

namespace Certificates

open CFSG.LocalAnalysis.GLTheoremA.H301B.Fi24PlanesNative in
theorem certificate101705 : fi24PlanesOK () = true :=
  CertificateChecks.KernelLC.Fi24PlA.planes

end Certificates
