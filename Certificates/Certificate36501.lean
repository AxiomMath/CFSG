module

public import Certificates.Data.GH74.McLGen45
import Certificates.Kernel.McLGen.Final

public section

namespace Certificates

open CertificateChecks

theorem certificate36501 : CFSG.Sporadic.McL.Gen45.mclGenCertificate () = true := KernelMcLGen.gen_cert

end Certificates
