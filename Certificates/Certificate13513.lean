module

public import Certificates.Data.B3Spor3.J2
public meta import Certificates.Data.B3Spor3.J2
import Certificates.Kernel.B3S3.J2Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem certificate13513 : check j2S3Data = true := KernelB3S3.J2.j2_ok

end Certificates
