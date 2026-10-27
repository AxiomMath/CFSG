module

public import Certificates.Data.D4HexLineChar
import Certificates.Kernel.S63K.K4239

public section

namespace Certificates

open CertificateChecks

theorem certificate4239 : CFSG.D4Hex.lineCharCheck = true := KernelS63.K4239.c4239

end Certificates
