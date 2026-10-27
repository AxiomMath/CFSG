module

public import Certificates.Kernel.Co1M.K42D
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

@[expose] noncomputable def t42F2 (q : Nat) : Bool := t42S (Nat.add (nat_lit 244) q)

end CFSG.KD.Co1M

#kc_slices CFSG.KD.Co1M.T42x2 CFSG.KD.Co1M.t42F2 122

end
