
module


public import Certificates.Certificate7019

public section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

theorem card_fix_orbit :
    Nat.card {w : Row // w ∈ MulAction.orbit J CFSG.Sporadic.J4Schreier.v ∧ tJ • w = w} =
      52349 :=
  Certificates.certificate7019

end CFSG.Quasithin.H13.J4
