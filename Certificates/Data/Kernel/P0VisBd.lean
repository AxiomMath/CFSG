module

public import Certificates.Data.CFSGNative.MonsterB.P0Rank

public section

namespace CFSG.KC.P0Vis

@[expose] def pairOK (p : Nat × Nat) : Bool := Nat.blt p.1 65536 && Nat.blt p.2 512

@[expose] def bdOK (dat : MonsterB.P0Rank.Data) : Bool :=
  dat.beta.all (·.all (Nat.blt · 512)) && dat.uConjL.all (·.all pairOK) &&
    dat.uConjT.all (·.all (Nat.blt · 512)) && dat.uSq.all pairOK && dat.uComm.all (·.all pairOK)

end CFSG.KC.P0Vis

end
