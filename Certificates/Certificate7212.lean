module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34QBridge
import CFSG.Certificates.Kernel.L34Q.Sound
import Certificates.Kernel.L34Q.Checks

public section

namespace Certificates

open CFSG.Quasithin CFSG.Quasithin.H13.Ch9.L34Q in
theorem certificate7212 :
    (∀ E : Subgroup (MulAut VM4), (∀ g ∈ E, ∃ p ∈ params, Realizes g p) → IsElemAbelian2 E →
      IsQuadratic E → Nat.card E ^ 4 * Nat.card (fixV E) ^ 3 ≤ 2 ^ 24) ∧
    (∀ E : Subgroup (MulAut VM4), (∀ g ∈ E, ∃ p ∈ params, Realizes g p) → IsElemAbelian2 E →
      IsQuadratic E → E ≠ ⊥ → Nat.card E < Nat.card (commV E)) :=
  CFSG.Quasithin.H13.Ch9.L34Q.KS.facts_of_checks CFSG.KD.L34Q.ch7212inv CFSG.KD.L34Q.ch7212cap
    CFSG.KD.L34Q.ch7212plus

end Certificates
