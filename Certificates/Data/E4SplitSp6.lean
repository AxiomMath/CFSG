module

public import Certificates.Data.E4QuatSp6Check
public import Certificates.Data.E4SplitCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def splitWord : List ℤ :=
  [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, -2, -2, 1, -2, 1, -2, 1]

@[expose] def splitWit (_ : Unit) : Equiv.Perm (Fin 36) := tab (evalCodes sp6Gens splitWord)

@[expose] def scheck (_ : Unit) : Bool :=
  splitCheck (L0 ()) (tab sp6Rep2) (rho ()) (jay ()) (ws ()) [splitWit ()]

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
