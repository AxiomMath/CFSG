module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.SigmaKDefs
import Certificates.Kernel.K272036.Fact

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J2Cz CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition in
theorem certificate272036 : ∀ σ : KK →* KK, ((σ (gK 0) : KK) : Model) = elY → ((σ (gK 1) : KK) : Model) = elX →
    ((σ (gK 2) : KK) : Model) = elZ * elX →
    (∀ k : KK, ((σ (σ k) : KK) : Model) = elA * (k : Model) * elA⁻¹) →
    ((σ (gK 3) : KK) : Model) = elT := K272036.forced

end Certificates
