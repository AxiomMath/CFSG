module

public import Certificates.Data.CFSGNative.Mathieu.M24
import Certificates.Kernel.Sporadic.Mathieu

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native in
theorem certificate3017 : check 24 m24Data = true := KernelSpor.Mathieu.m24

end Certificates
