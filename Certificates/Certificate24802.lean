module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck
import CFSG.Certificates.Kernel.TabPackOut

public section

open CFSG.EvenSporadicStandard.M22Std.OutCheck

namespace CertificateChecks.Batch24802

open CFSG.EvenSporadicStandard.M22Std.OutCheck

set_option maxHeartbeats 0 in
theorem uniqRepOK_0 : uniqRepOK s0Tabs f1Tabs s0Reps = true := by
  rw [CFSG.KTabPack.Out.uniqRepOK_eq CFSG.KTabPack.Out.s0_W CFSG.KTabPack.Out.f1_W
    CFSG.KTabPack.Out.reps_W]
  decide +kernel

end CertificateChecks.Batch24802

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.OutCheck in
theorem certificate24802 : uniqRepOK s0Tabs f1Tabs s0Reps = true :=
  CertificateChecks.Batch24802.uniqRepOK_0

end Certificates
