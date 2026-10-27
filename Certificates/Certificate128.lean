module

public import Certificates.Kernel.OmegaEight.E4O8NbrGlue
public import Certificates.Certificate3119

public section

namespace Certificates

open CertificateChecks

theorem certificate128 : CFSG.ClassicalInvolution.Q3.TL4.E4O8.twoCheck () = true := KernelO8.twoCheck_k

end Certificates
