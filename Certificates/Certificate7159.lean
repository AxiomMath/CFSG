module

public import CFSG.Quasithin.H13.NQCatT513U35MC
import Certificates.Kernel.U35Pk.Glue
import Certificates.Kernel.U35Pk.Checks

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.NQCat.T513 CFSG.RankThree.PartTwo.KFacts in
theorem certificate7159 : Nat.card ↥U35.T0 = 16 ∧
    (∀ x ∈ U35.T0, (∀ y ∈ U35.T0, x * y = y * x) → x = 1 ∨ x = U35.z0) ∧
    ∀ x ∈ (psuConj CFSG.Quasithin.H13.KGU35.f25Data).range, Odd (orderOf x) →
      (∀ t ∈ U35.T0, ∃ a : ℤ, ∃ t' ∈ U35.T0, MulAut.conj t * x = x ^ a * MulAut.conj t') →
        x U35.z0 = U35.z0 :=
  U35Pk.certificate7159_of_facts
    (U35Pk.facts_of_sound (CFSG.Certificates.U35Pk.u35Pk_sound _root_.U35Pk.u35PkCheck_true))

end Certificates
