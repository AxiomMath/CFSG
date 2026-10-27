module

public import Certificates.Data.Kernel.Spor.ONK

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def negAt (K NEG : Nat → Nat) (n i : Nat) : Bool :=
  strictB (tab NEG i) fun j => bAnd(Nat.blt j n,
    bAnd(Nat.beq (key K j) (vneg (key K i)), Nat.beq (tab NEG j) i))

@[expose] noncomputable def negRange (K NEG : Nat → Nat) (n lo cnt : Nat) : Bool :=
  allBlk lo (negAt K NEG n) cnt

end CFSG.KS.ON

end
