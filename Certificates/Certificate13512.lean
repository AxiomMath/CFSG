module

public import Certificates.Data.B3Spor3.M24
public meta import Certificates.Data.B3Spor3.M24
import Certificates.Kernel.B3S3.M24Facts
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem certificate13512 : check m24S3Data = true := KernelB3S3.M24.m24_ok

end Certificates
