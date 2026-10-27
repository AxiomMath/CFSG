module

public import Certificates.Kernel.Co1M.K42D
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

@[expose] noncomputable def t42F0 (q : Nat) : Bool := t42S q

end CFSG.KD.Co1M

#kc_slices CFSG.KD.Co1M.T42x0 CFSG.KD.Co1M.t42F0 122

end
