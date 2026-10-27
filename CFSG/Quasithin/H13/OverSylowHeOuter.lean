module

public import Certificates.Certificate589205
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.LocDbl.OverHe

open CFSG.Sporadic.He (J)

theorem heAutInner_J :
    ∀ S B : Subgroup J, Nat.card S = 2 ^ 10 → S ≤ Subgroup.normalizer (B : Set J) →
      Nat.card B = 69120 → ∀ f : MulAut J, (AutInner.aimg (P := J) f B : Subgroup J) = B →
        ∃ k : J, ∀ x, f x = k * x * k⁻¹ :=
  Certificates.certificate589205

end CFSG.Quasithin.H13.LocDbl.OverHe
