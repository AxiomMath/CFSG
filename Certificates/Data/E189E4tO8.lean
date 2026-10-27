module

public import Certificates.Data.E4QuatO8Check
public import Certificates.Data.E189E4tCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.ClassicalInvolution.Q3.TL4.E4A

@[expose] def tcheck (_ : Unit) : Bool := tCheckA 360 (L0A ()) (xA 0) (u0A ()) (v0A ()) (wsA ())

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
