module

public import Certificates.Kernel.Co1M.K45D
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

@[expose] noncomputable def st45F0 (q : Nat) : Bool := st45S q

end CFSG.KD.Co1M

#kc_slices CFSG.KD.Co1M.ST45x0 CFSG.KD.Co1M.st45F0 60

end
