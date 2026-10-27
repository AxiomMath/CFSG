module

public import Certificates.Data.GH74.McLWeights
import Certificates.Kernel.Ivk8McL.Wt5254Final

public section

namespace Certificates

open CertificateChecks

theorem certificate5254 : CFSG.Sporadic.Recognition.McLAS.wtCertificate () = true := KernelIvk8McLWt.wtCheck_true

end Certificates
