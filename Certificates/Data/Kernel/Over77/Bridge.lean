module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Over77

open CFSG.KC.Enum

@[expose] noncomputable def bridgeK (a : Nat) (d : Array Nat) : Bool :=
  allN (nat_lit 77) (fun i => Nat.beq (pg (nat_lit 7) (nat_lit 127) a i) (d.getD i (nat_lit 0)))

end CFSG.KC.Over77

end
