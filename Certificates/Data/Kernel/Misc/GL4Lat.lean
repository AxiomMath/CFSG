module

public import Certificates.Data.Kernel.Misc.GL4Code

public section

namespace CFSG.KC.Misc.GL4

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def invW (c d : Nat) : Bool :=
  andB (Nat.blt c (nat_lit 65536)) (andB (Nat.blt d (nat_lit 65536)) (Nat.beq (mul4F c d) id4))

@[expose] noncomputable def escAtM (M : Nat → Nat → Nat) (EP : Nat → Nat) (N : Nat)
    (EA : Nat → Nat) (NA : Nat) (WG : Nat → Nat) (nW R : Nat) (WX : Nat → Nat) : Bool :=
  letB (fld R (nat_lit 0) (nat_lit 15)) fun a => letB (EA a) fun r =>
    andB (Nat.blt a NA) (allN nW fun i => wordOKM M EP N r (WG i) (WX i))

end CFSG.KC.Misc.GL4

end
