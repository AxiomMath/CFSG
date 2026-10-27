module

public import Certificates.Data.D4HexOverCheck
import Certificates.Kernel.S63K.O4238

public section

namespace Certificates

open CertificateChecks

theorem certificate4238 : CFSG.D4Hex.overCheck = true := KernelS63.O4238.c4238

end Certificates
