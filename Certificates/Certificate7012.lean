
module

public import Certificates.Certificate7012Base

public import CFSG.Quasithin.H13.J4CoreInputs
import Certificates.Kernel.J4F2.H13

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4 in
open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native CFSG.Certificates.ExtraspecialNF in
theorem certificate7012 :
    pChecks = true := KernelJ4F2.c7012

end Certificates
