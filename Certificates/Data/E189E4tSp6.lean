module

public import Certificates.Data.E4QuatSp6Check
public import Certificates.Data.E189E4tCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def tcheck (_ : Unit) : Bool := tCheck (L0 ()) (tab sp6Rep2) (rho ()) (jay ()) (ws ())

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
