module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowSylTests
import Certificates.Kernel.LocalComp.HeSyl.Check8330

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.AS81.HeSylow

open CFSG in
theorem certificate15041 : CFSG.ComponentClassification.AS81.HeSylow.heSylowCheckS = true := by
  unfold heSylowCheckS
  rw [KernelLC.HeSyl.sylCheck8330S_true, KernelLC.HeSyl.sylCheckRestrict_true,
    KernelLC.HeSyl.sylCheck16_true]
  rfl

end Certificates
