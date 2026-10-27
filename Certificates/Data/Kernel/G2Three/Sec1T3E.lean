module

public import Certificates.Data.Kernel.G2Three.Sec1T3

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

@[expose] noncomputable def latKey (L OR k : Nat) : Nat :=
  Nat.add (Nat.shiftLeft (ordAt OR k) 128) (fld(L, Nat.mul 128 k, M128))

@[expose] noncomputable def latSortK (L OR m : Nat) : Bool :=
  allBelow m 7 fun k => bIf(Nat.blt (Nat.succ k) m, Nat.blt (latKey L OR k) (latKey L OR (Nat.succ k)),
    true)

end CFSG.KD.G2Three.Sec1T3

end
