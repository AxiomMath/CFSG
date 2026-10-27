module

public import Certificates.Data.CFSGNative.J4Tree.M4Type
import Certificates.Kernel.J4M4.Checks

public section

namespace Certificates

open CertificateChecks

theorem certificate7952 : CFSG.J4Tree.M4.codeChecks () = true := KernelJ4M4.codeChecks_ok

end Certificates
