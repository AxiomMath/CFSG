module

public import Certificates.Data.Kernel.Co2Smith.Rows

public section

namespace CFSG.KC.Co2Smith

open CFSG.KC.Co2InvS

@[expose] noncomputable def c0PredK (F Z : Nat) (R : List Nat) (G : Nat) : Bool :=
  (!(commK G F && eqK (mulV G G) IDP && !eqK G IDP) || eqK G Z) &&
    R.any fun Y => eqK (mulV Y G) (mulV G Z)

@[expose] noncomputable def c0K (L Fm : Nat → Nat) (F Z : Nat) (R : List Nat)
    (W0 : List (Nat × Nat × List Nat)) (W1 W2 : List (Nat × List Nat)) : Bool :=
  W0.all fun e => W1.all fun e₁ => W2.all fun e₂ =>
    c0PredK F Z R (mulV (mulV (mulV (wK L e.2.2) (Fm e.2.1)) (wK L e₁.2)) (wK L e₂.2))

end CFSG.KC.Co2Smith
