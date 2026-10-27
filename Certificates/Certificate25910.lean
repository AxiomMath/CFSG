module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3S6Check

public section

open CFSG.EvenSporadicStandard.M22Std.S6Check

namespace CertificateChecks.Batch25910

open CFSG.EvenSporadicStandard.M22Std.S6Check

set_option maxHeartbeats 0 in
theorem prop1 : S6Prop1 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem prop2 : S6Prop2 := by
  decide +kernel

theorem check_0 : s6Check = true := decide_eq_true ⟨prop1, prop2⟩

end CertificateChecks.Batch25910

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.S6Check in
theorem certificate25910 : s6Check = true := CertificateChecks.Batch25910.check_0

end Certificates
