module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.M23SylowCheck
import CFSG.Certificates.Kernel.TabPackM23

public section

open CFSG.EvenSporadicStandard.Wong77.M23Sylow

namespace CertificateChecks.Batch24160

open CFSG.EvenSporadicStandard.Wong77.M23Sylow

set_option maxHeartbeats 0 in
theorem sylowOK_0 : sylowOK gensTab = true := by
  rw [CFSG.KTabPack.M23.sylowOK_eq]
  exact CFSG.KTabPack.sylowT_of_N (by decide) CFSG.KTabPack.M23.gens_W (by decide +kernel)

theorem subOK_1 : subOK (span gensTab) (elemTabs 0) = true := by decide +kernel

theorem subOK_2 : subOK (span gensTab) (elemTabs 1) = true := by decide +kernel

end CertificateChecks.Batch24160

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Wong77.M23Sylow in
theorem certificate24160 : (sylowOK gensTab = true) ∧
    (subOK (span gensTab) (elemTabs 0) = true) ∧ (subOK (span gensTab) (elemTabs 1) = true) :=
  ⟨CertificateChecks.Batch24160.sylowOK_0, CertificateChecks.Batch24160.subOK_1,
    CertificateChecks.Batch24160.subOK_2⟩

end Certificates
