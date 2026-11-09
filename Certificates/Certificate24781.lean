module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabCheck
import CFSG.Certificates.Kernel.TabPackM22

public section

open CFSG.EvenSporadicStandard.M22Std.TabCheck

namespace CertificateChecks.Batch24781

open CFSG.EvenSporadicStandard.M22Std.TabCheck

set_option maxHeartbeats 0 in
theorem sylowOK_0 : sylowOK gensTab = true := by
  rw [CFSG.KTabPack.M22.sylowOK_eq]
  exact CFSG.KTabPack.sylowT_of_N (by decide) CFSG.KTabPack.M22.gens_W (by decide +kernel)

theorem subOK_1 : subOK (span gensTab) (elemTabs 0) = true := by decide +kernel

theorem subOK_2 : subOK (span gensTab) (elemTabs 1) = true := by decide +kernel

end CertificateChecks.Batch24781

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.TabCheck in
theorem certificate24781 : (sylowOK gensTab = true) ∧
    (subOK (span gensTab) (elemTabs 0) = true) ∧ (subOK (span gensTab) (elemTabs 1) = true) :=
  ⟨CertificateChecks.Batch24781.sylowOK_0, CertificateChecks.Batch24781.subOK_1,
    CertificateChecks.Batch24781.subOK_2⟩

end Certificates
