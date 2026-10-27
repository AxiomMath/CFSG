module

public import Certificates.Data.E4QuatSp6Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

@[expose] def wOne (_ : Unit) : Equiv.Perm (Fin 36) := (ws ()).getD 1 1

@[expose] def uOne (_ : Unit) : Equiv.Perm (Fin 36) := twin () * (rho () * jay ()) * (twin ())⁻¹

@[expose] def uTwo (_ : Unit) : Equiv.Perm (Fin 36) := wOne () * rho () * (wOne ())⁻¹

@[expose] def sp6ThreeCheck (_ : Unit) : Bool :=
  decide (rho () * uOne () = uOne () * rho ()) && decide (rho () * uTwo () = uTwo () * rho ()) &&
    decide (uOne () * uTwo () = uTwo () * uOne ()) && !decide (rho () ^ 2 = 1) &&
    !decide (uOne () ^ 2 = 1) && !decide (uTwo () ^ 2 = 1) && !decide (uTwo () ∈ L0 ()) &&
    !decide ((twin ())⁻¹ * uTwo () * twin () ∈ L0 ())

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
