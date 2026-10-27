module

public import Certificates.Data.E4QuatSp6Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C

@[expose] def three (_ : Unit) : Equiv.Perm (Fin 36) := tab (evalCodes sp6CentGens2 [2, 1, 2, 1])

@[expose] def linkCheck (_ : Unit) : Bool :=
  decide (twin () * tab sp6Rep2 = tab sp6Rep2 * twin ()) && decide (three () ^ 3 = 1) &&
    norms (L0 ()) (rho ()) (jay ()) (three ()) && !decide (three () * rho () = rho () * three ())

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
