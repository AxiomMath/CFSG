module

public import CFSG.Quasithin.H13.J4QuotGroupInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4
open CFSG.Quasithin.H13.J4.Native

namespace CertificateChecks.Batch7016

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4
open CFSG.Quasithin.H13.J4.Native

private theorem localChecks_eq_0 :
    localChecks = true := by
  decide +kernel

end CertificateChecks.Batch7016

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4 in
open CFSG.Quasithin.H13.J4.Native in
theorem certificate7016 :
    localChecks = true := by
  exact CertificateChecks.Batch7016.localChecks_eq_0

end Certificates
