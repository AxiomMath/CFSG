module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Data
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Data
import Certificates.Certificate10019
import Certificates.Kernel.C12643.Check

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155 in
theorem certificate12643 : ks155OK () = true := KernelC12643.ks155OK_K

end Certificates

end
