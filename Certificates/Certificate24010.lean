module

public import CFSG.Sporadic.Recognition.HSMultiplierInputs
import Certificates.Kernel.HSMult.Tab
import Certificates.Kernel.HSMult.Bounds

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Recognition.HSMultiplier in
theorem certificate24010 : (hsTabCheck = true) ∧
    (Finite (PG 6 hsRels) ∧ Nat.card (PG 6 hsRels) ≤ 44352000) ∧
    (Finite HSCover ∧ Nat.card HSCover ≤ 88704000) :=
  ⟨KernelHSMult.tab, KernelHSMult.card_presented, KernelHSMult.card_cover⟩

end Certificates
