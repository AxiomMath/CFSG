module

public import Certificates.Data.J4M3.Native
import Certificates.Kernel.J4F2.J4M3SixGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J4M3 in
theorem certificate7245 : (chkU5 () = true) ∧ (chkN () = true) ∧ (chkPts () = true) ∧ (chkP () = true) ∧
    (chkQ () = true) ∧ (chkC () = true) := KernelJ4F2.c7245

end Certificates
