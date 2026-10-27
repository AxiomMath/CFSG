module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HSThreeData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HSThreeData
import Certificates.Kernel.HS100.HS3Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor in
theorem certificate12612 : hsThreeOK () = true := KernelHS100.hsThree

end Certificates
