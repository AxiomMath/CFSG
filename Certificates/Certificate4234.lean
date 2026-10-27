module

public import Certificates.Data.D4HexLinkCheck
import Certificates.Kernel.S63K.L4234

public section

namespace Certificates

open CertificateChecks

theorem certificate4234 : CFSG.D4Hex.linkCheck = true := KernelS63.L4234.c4234

end Certificates
