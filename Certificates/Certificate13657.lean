module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData

public section

open CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace CertificateChecks.Batch13657

open CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option maxHeartbeats 0 in
private theorem e6_three_sc_check_0 : e6ThreeScCheck () = true := by decide +kernel

end CertificateChecks.Batch13657

namespace Certificates

open CertificateChecks

theorem certificate13657 : CFSG.HardMathSupport.Timmesfeld.CrossChar.e6ThreeScCheck () = true := by
  exact CertificateChecks.Batch13657.e6_three_sc_check_0

end Certificates
