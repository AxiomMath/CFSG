module

public import Certificates.Data.L43TwinQ8
import Certificates.Kernel.L43Q8.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate397502 : L43TwinQ8.check () = true := KernelL43Q8.check_true

end Certificates
