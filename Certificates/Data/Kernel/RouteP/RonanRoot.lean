module

public import Certificates.Data.Kernel.RouteP.Ronan

public section

namespace CFSG.KC.RouteP

@[expose] noncomputable def rootOK (E : Nat → Nat) (lo hi : Nat) : Bool :=
  allI (Nat.sub (Nat.sub hi lo) (nat_lit 1)) fun i =>
    Nat.blt (ePar (E (Nat.add (Nat.add lo (nat_lit 1)) i))) (Nat.add (Nat.add lo (nat_lit 1)) i)

end CFSG.KC.RouteP

end
