module

public import CFSG.Quasithin.H13.HeAutInnerCore
import Certificates.Kernel.He7030.HeA
public import CFSG.Sporadic.He.Setup

public section

open CFSG.Quasithin.H13.LocDbl

public section

namespace Certificates

open CFSG.Quasithin.H13.LocDbl in
theorem certificate589205 : 
    ∀ S B : Subgroup CFSG.Sporadic.He.J, Nat.card S = 2 ^ 10 →
      S ≤ Subgroup.normalizer (B : Set CFSG.Sporadic.He.J) → Nat.card B = 69120 →
      ∀ f : MulAut CFSG.Sporadic.He.J,
        (AutInner.aimg (P := CFSG.Sporadic.He.J) f B : Subgroup CFSG.Sporadic.He.J) = B →
          ∃ k : CFSG.Sporadic.He.J, ∀ x, f x = k * x * k⁻¹ := by
  exact CFSG.KD.He7030.heAutInner_JK

end Certificates

end

end
