module

public import Certificates.Data.Kernel.Misc.RuScan

public section

namespace CFSG.KC.Misc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan

@[expose] noncomputable def fixL (LR TR : Nat → Nat) (l x : Nat) : Bool :=
  allN (rcnt (LR l)) (fun k =>
    Nat.beq (apP (TR (Nat.add (roff (nat_lit 4060) (nat_lit 48720) (LR l)) k)) x) x)

end CFSG.KC.Misc.RuBigZ

end
