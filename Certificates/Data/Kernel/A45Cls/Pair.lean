module

public import Certificates.Data.Kernel.A45Cls.Defs

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind

@[expose] noncomputable def invFixK (n w f P : Nat) : Bool :=
  bAnd(isInvK n w P, Nat.beq (fixK n w P) f)

@[expose] noncomputable def prodK (n w fa fb N : Nat) (T : Nat → Nat) (t : Nat) : Bool :=
  allN N fun i => strictB (T i) fun u =>
    !(bAnd(invFixK n w fa u, !Nat.beq u t)) || invFixK n w fb (pcomp n w (mask w) u t)

end CFSG.KC.A45Cls

end
