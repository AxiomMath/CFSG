module

public import CFSG.Timmesfeld.Exceptional.DeepQTabInputs

public section

open CFSG.Timmesfeld.Moufang.Deep

namespace CertificateChecks.Batch8056

open CFSG.Timmesfeld.Moufang.Deep

private theorem tabA_inv_0 :
    (∀ x, ofTab tabAi (ofTab tabA x) = x) ∧ ∀ x, ofTab tabA (ofTab tabAi x) = x := by
  decide +kernel

private theorem tabB_inv_1 :
    (∀ x, ofTab tabBi (ofTab tabB x) = x) ∧ ∀ x, ofTab tabB (ofTab tabBi x) = x := by
  decide +kernel

private theorem tabQ_inv_2 :
    (∀ x, ofTab tabQi (ofTab tabQ x) = x) ∧ ∀ x, ofTab tabQ (ofTab tabQi x) = x := by
  decide +kernel

end CertificateChecks.Batch8056

namespace Certificates

open CertificateChecks

open CFSG.Timmesfeld.Moufang.Deep in
theorem certificate8056 : ((∀ x, ofTab tabAi (ofTab tabA x) = x) ∧ ∀ x, ofTab tabA (ofTab tabAi x) = x)
    ∧ ((∀ x, ofTab tabBi (ofTab tabB x) = x) ∧ ∀ x, ofTab tabB (ofTab tabBi x) = x)
    ∧ ((∀ x, ofTab tabQi (ofTab tabQ x) = x) ∧ ∀ x, ofTab tabQ (ofTab tabQi x) = x) := by
  exact ⟨CertificateChecks.Batch8056.tabA_inv_0, CertificateChecks.Batch8056.tabB_inv_1, CertificateChecks.Batch8056.tabQ_inv_2⟩

end Certificates
