module

public import Certificates.Data.D4HexLocCheck
import Certificates.Kernel.S63K.P4237

public section

namespace Certificates

open CertificateChecks

theorem certificate4237 : CFSG.D4Hex.locCheck = true := KernelS63.P4237.c4237

end Certificates
