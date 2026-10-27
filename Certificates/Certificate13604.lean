module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataF4

public section

open CFSG.HardMathSupport.Timmesfeld.Steinberg

namespace CertificateChecks.Batch13604

open CFSG.HardMathSupport.Timmesfeld.Steinberg

private theorem f4_three_check_0 : f4ThreeCheck () = true := by decide +kernel

end CertificateChecks.Batch13604

namespace Certificates

open CertificateChecks

theorem certificate13604 : CFSG.HardMathSupport.Timmesfeld.Steinberg.f4ThreeCheck () = true := by
  exact CertificateChecks.Batch13604.f4_three_check_0

end Certificates
