module

public import Certificates.Data.CFSGNative.Mathieu.M12
import Certificates.Kernel.Sporadic.Mathieu

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native in
theorem certificate3086 : check 12 m12Data = true := KernelSpor.Mathieu.m12

end Certificates
