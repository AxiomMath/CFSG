module

public import Certificates.Kernel.B433Alt.Data.St
public import Certificates.Data.Kernel.B433Alt.Struct

public section

namespace CFSG.KD.B4A

@[expose] noncomputable def stOK (r : Nat) : Bool := CFSG.KC.B4A.foldOK LP RD RW PW RJ SS r

end CFSG.KD.B4A

end
