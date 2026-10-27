module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck
import CFSG.Certificates.Kernel.TabPackOut

public section

open CFSG.EvenSporadicStandard.M22Std.OutCheck

namespace CertificateChecks.Batch24802

open CFSG.EvenSporadicStandard.M22Std.OutCheck

set_option maxHeartbeats 0 in
theorem uniqOK_0 : uniqOK s0Tabs f1Tabs = true := by
  rw [CFSG.KTabPack.Out.uniqOK_eq CFSG.KTabPack.Out.s0_W CFSG.KTabPack.Out.f1_W]
  decide +kernel

end CertificateChecks.Batch24802

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.OutCheck in
theorem certificate24802 : uniqOK s0Tabs f1Tabs = true := CertificateChecks.Batch24802.uniqOK_0

end Certificates
