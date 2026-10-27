module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.RuIdx2

open CFSG.KC.Enum

@[expose] noncomputable def wltK (W : Nat) : Bool :=
  allBlk (nat_lit 0) (fun k => Nat.blt fld(W, Nat.add (nat_lit 8) (Nat.shiftLeft k (nat_lit 2)), nat_lit 15)
    (nat_lit 10)) (Nat.land W (nat_lit 255))

end CFSG.KC.RuIdx2

end
