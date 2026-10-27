module

public import Certificates.Data.Kernel.Misc.RuInv

public section

namespace CFSG.KC.Misc.RuPair

open CFSG.KC.Enum CFSG.KC.Misc.RuInv

@[expose] noncomputable def commK (G H GI HI T Z : Nat) : Bool :=
  allN (nat_lit 4060) (fun x =>
    Nat.beq (apP G (apP H (apP GI (apP HI (apP T x))))) (apP T (apP Z x)))

end CFSG.KC.Misc.RuPair

end
