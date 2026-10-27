module

public import Certificates.Data.CFSGNative.Mathieu.M22
import Certificates.Kernel.Sporadic.Mathieu

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native in
theorem certificate3029 : check 22 m22Data = true := KernelSpor.Mathieu.m22

end Certificates
