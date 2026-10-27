module

public import Certificates.Data.H9FourJ
import all Certificates.Data.H9Four
import all Certificates.Data.H9FourJ

public section

open CFSG.Quasithin.H13.H9Four

namespace CertificateChecks.Batch7140

open CFSG.Quasithin.H13.H9Four

private theorem d8Check_0 : d8Check = true := by decide +kernel

end CertificateChecks.Batch7140

namespace Certificates

open CertificateChecks.Batch7140 in
open CFSG.Quasithin.H13.H9Four in
theorem certificate7140 : d8Check = true :=
  d8Check_0

end Certificates
