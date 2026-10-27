module

public import Certificates.Data.OmegaInv
import Certificates.Certificate2012
import Certificates.Kernel.A45Cls.CheckE16

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaInv in
theorem certificate442020 : ∀ S : Subgroup (Equiv.Perm (Fin 45)), S ≤ QA45.originalSubgroup → Nat.card S = 16 →
    (∀ x ∈ S, x * x = 1) →
    ((∀ x ∈ S, fixCnt x = 45 ∨ fixCnt x = 13 ∨ fixCnt x = 5) ∨ ∃ x ∈ S, fixCnt x = 15) ∧
      ∀ F : Finset (Equiv.Perm (Fin 45)), (∀ x ∈ F, x ∈ S ∧ fixCnt x = 15) → F.card ≤ 4 := KernelA45.omegaCE16_model

end Certificates
