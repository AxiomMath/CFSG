module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourNonInnerData

public section

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

namespace CertificateChecks.Batch13616

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

private theorem check_0 : e6NonInnerCheck () = true := by
  decide +kernel

end CertificateChecks.Batch13616

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 in
theorem certificate13616 : e6NonInnerCheck () = true := by
  exact CertificateChecks.Batch13616.check_0

end Certificates
