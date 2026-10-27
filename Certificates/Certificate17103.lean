module

public import CFSG.Blueprint.NativeSporadic
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Seven
import Certificates.Certificate3115
import Certificates.Certificate3116
import Certificates.Certificate3117
import Certificates.Certificate16960

public section

namespace Certificates

open CFSG.Blueprint in
theorem certificate17103 :
    ∀ s : NativeSporadic.Co2, orderOf s = 7 → ∀ M : Subgroup NativeSporadic.Co2,
      M ≤ Subgroup.centralizer ({s} : Set NativeSporadic.Co2) → Odd (Nat.card M) →
        ¬ 7 ∣ Nat.card M → M = ⊥ :=
  fun s hs _ hM hodd h7 =>
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Seven.co2_seven_eq_bot s hs hM hodd h7

end Certificates
