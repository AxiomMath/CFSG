module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44GolayCheck

public section

namespace CertificateChecks.Batch25300

open CFSG.EvenSporadicStandard.TwoFi22.DS81 in
theorem golay_aut_check_0 : golayAutCheck = true := by
  decide +kernel

end CertificateChecks.Batch25300

namespace Certificates

open CertificateChecks

theorem certificate25300 : CFSG.EvenSporadicStandard.TwoFi22.DS81.golayAutCheck = true := CertificateChecks.Batch25300.golay_aut_check_0

end Certificates
