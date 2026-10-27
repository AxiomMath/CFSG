module

public import Certificates.Kernel.Co1M.K73D
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

@[expose] noncomputable def ta73F5 (q : Nat) : Bool := ta73S (Nat.add (nat_lit 150) q)

end CFSG.KD.Co1M

#kc_slices CFSG.KD.Co1M.TA73x5 CFSG.KD.Co1M.ta73F5 29

end
