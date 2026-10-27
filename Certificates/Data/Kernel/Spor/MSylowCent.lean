module

public import Certificates.Data.Kernel.Spor.MSylow

public section

namespace CFSG.KS.MSyl

open CFSG.KC.Enum

@[expose] noncomputable def centBadP (n w m I Z : Nat) (PT : List Nat) (g : Nat) : Bool :=
  bAnd(commAllP n w m g PT, bAnd(bIf(Nat.beq g I, false, true), bIf(Nat.beq g Z, false, true)))

end CFSG.KS.MSyl

end
