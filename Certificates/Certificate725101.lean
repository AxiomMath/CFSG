module

public import Certificates.Data.J4M3.Three
import Certificates.Kernel.J4F2.J4M3Three

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J4M3 in
theorem certificate725101 : chkY3 () = true := KernelJ4F2.c725101

end Certificates
