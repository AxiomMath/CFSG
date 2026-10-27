module

public import Certificates.Data.Kernel.Spor.HKeyU
public import Certificates.Kernel.E27J3Syl.D
public import Certificates.Kernel.E27J3Syl.DV

public section

namespace CFSG.KD.E27J3S

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH

@[expose] noncomputable def jHu (i : Nat) : Bool := Nat.beq (hkeyU 6156 13 (mask 13) (SE.T i)) (SEV i)

@[expose] noncomputable def c131001Hu (k : Nat) : Bool := slK SE.cnt jHu (Nat.mul 16 k) 16

end CFSG.KD.E27J3S

end
