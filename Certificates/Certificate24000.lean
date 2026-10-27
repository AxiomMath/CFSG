module

public import CFSG.Sporadic.Recognition.M23MultiplierInputs
import Certificates.Kernel.M23Mult.Bounds

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Recognition.M23Multiplier in
theorem certificate24000 : (m23TabCheck = true) ∧
    (Finite (PG 6 m23Rels) ∧ Nat.card (PG 6 m23Rels) ≤ 10200960) ∧
    (Finite M23Cover ∧ Nat.card M23Cover ≤ 10200960) :=
  ⟨KernelM23Mult.tab, KernelM23Mult.card_presented, KernelM23Mult.card_cover⟩

end Certificates
