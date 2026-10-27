module

public import CFSG.Quasithin.H13.J4QuotInputs
import Certificates.Kernel.J4F2.H13Quot

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4 in
open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native Matrix in
theorem certificate7015 :
    (quotChecks = true)
    ∧ (imageChecks = true) := KernelJ4F2.c7015

end Certificates
