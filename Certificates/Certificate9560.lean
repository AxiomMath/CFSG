module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22AltData
import Certificates.Kernel.Fi22Alt.Final

public section

namespace Certificates

open CFSG.AGLEmbedding.KFactProofs.Fi22Alt in
theorem certificate9560 : fi22AltCheck = true :=
  CertificateChecks.KernelFi22Alt.alt_ok

end Certificates
