module

public import Certificates.Data.CFSGNative.J3.Data
import Certificates.Kernel.Sporadic.J3K.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J3.Native in
theorem certificate3169 : CFSG.Sporadic.J3.Native.check j3Data 3 = true := KernelSpor.J3K.j3_cert

end Certificates
