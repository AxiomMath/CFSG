module

public import Certificates.Kernel.Co1M.K45D
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

@[expose] noncomputable def st45F1 (q : Nat) : Bool := st45S (Nat.add (nat_lit 60) q)

end CFSG.KD.Co1M

#kc_slices CFSG.KD.Co1M.ST45x1 CFSG.KD.Co1M.st45F1 60

end
