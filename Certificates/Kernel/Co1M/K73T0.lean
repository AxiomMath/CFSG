module

public import Certificates.Kernel.Co1M.K73D
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

@[expose] noncomputable def ta73F0 (q : Nat) : Bool := ta73S q

end CFSG.KD.Co1M

#kc_slices CFSG.KD.Co1M.TA73x0 CFSG.KD.Co1M.ta73F0 30

end
