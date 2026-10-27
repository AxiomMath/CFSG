module

public import Certificates.Data.E4QuatSp6Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C

@[expose] def ngWit (_ : Unit) : List (Equiv.Perm (Fin 36)) :=
  ([[-1, -1, -1, -1], [-3, -1, -1, -3, -1]] : List (List ℤ)).map fun w =>
    tab (evalCodes sp6CentGens2 w)

@[expose] def ngBad (L : List (Equiv.Perm (Fin 36))) (r j : Equiv.Perm (Fin 36))
    (ys : List (Equiv.Perm (Fin 36))) (c : Equiv.Perm (Fin 36)) : Bool :=
  norms L r j c && !(decide (c * r = r * c) && decide (c * j = j * c)) &&
    ys.all (fun y => decide (c * y = y * c)) && decide (c ^ 9 = 1)

@[expose] def ngCheck (_ : Unit) : Bool :=
  let L := L0 ()
  let r := rho ()
  let j := jay ()
  let ys := ngWit ()
  ys.all (fun y => decide (y ^ 3 = 1) && decide (y * r = r * y) && decide (y * j = j * y)) &&
    (enumeration sp6CentQ2).all fun c => !ngBad L r j ys c

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
