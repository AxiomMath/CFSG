module

public import Certificates.Data.OmegaInv
import Certificates.Certificate2012
import Certificates.Kernel.A45Cls.CheckInv

public section

namespace Certificates

open CertificateChecks

theorem certificate442007 : OmegaInv.check () = true := KernelA45.omegaInv_check

end Certificates
