
module

public import Certificates.Certificate8066Base
import all Certificates.Certificate8066Base

public import CFSG.Quasithin.Background.Sp4InfA6BasicInputs
import all CFSG.Quasithin.Background.Sp4InfA6BasicInputs
import all CFSG.Quasithin.Background.Sp4InfA6BasicBase

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf Equiv
open scoped Pointwise

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf Equiv in
open scoped Pointwise in
theorem certificate8066 : (Nat.card q1 = 24)
    ∧ (Nat.card q2 = 24)
    ∧ (Nat.card s0 = 8)
    ∧ (Nat.card (alternatingGroup (Fin 6)) = 360)
    ∧ (∀ g : Perm (Fin 6), (∀ x, bs0 x = true → bs0 (g * x * g⁻¹) = true) →
        (∀ x, bq1 x = true → bq1 (g * x * g⁻¹) = true) ∧
          ∀ x, bq2 x = true → bq2 (g * x * g⁻¹) = true) := by
  exact ⟨CertificateChecks.Batch8066.card_q1_0, CertificateChecks.Batch8066.card_q2_1, CertificateChecks.Batch8066.card_s0_2, CertificateChecks.Batch8066.card_alt_six_3,
    CertificateChecks.Batch8066.fix_of_normalizes_s0_4⟩

end Certificates
