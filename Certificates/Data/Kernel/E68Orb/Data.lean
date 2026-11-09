module

public import Init
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KC.SLOrb E68OT "Certificates/Data/Kernel/E68Orb/orb.bin" 768 4 364488
  10677560035281676441

public section

namespace CFSG.KC.SLOrb

@[expose] noncomputable def E68R (k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (E68OT (Nat.shiftRight k 5)) (Nat.mul (Nat.land k 31) 192))
    6277101735386680763835789423207666416102355444464034512895

@[expose] noncomputable def E68R24 (k : Nat) : Nat := E68R k

@[expose] noncomputable def E68R23 (k : Nat) : Nat := E68R (Nat.add 11392 k)

end CFSG.KC.SLOrb

end
