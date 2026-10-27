module

public import Certificates.Data.D4HexAutCheck
import Certificates.Kernel.S63K.H4240

public section

namespace Certificates

open CertificateChecks

theorem certificate4240 : CFSG.D4Hex.autCheck = true := KernelS63.H4240.c4240

end Certificates
