module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheckData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheckData
import Certificates.Kernel.J4M2.C12632

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck in
theorem certificate12632 : kCheck = true := KernelJ4M2.c12632

end Certificates
