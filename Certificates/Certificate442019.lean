module

public import Certificates.Data.OmegaQ2m
import Certificates.Certificate2012
import Certificates.Kernel.A45Cls.CheckInv

public section

namespace Certificates

open CertificateChecks

theorem certificate442019 : OmegaQ2m.check () = true := KernelA45.omegaQ2m_check

end Certificates
