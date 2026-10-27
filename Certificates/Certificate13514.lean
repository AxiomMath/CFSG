module

public import Certificates.Data.B3Spor3.HS
public meta import Certificates.Data.B3Spor3.HS
import Certificates.Kernel.B3S3.HSFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem certificate13514 : check hsS3Data = true := KernelB3S3.HS.hs_ok

end Certificates
