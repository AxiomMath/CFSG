module

public import Certificates.Data.Kernel.Fi22S0.Kill

public section

namespace CFSG.KC.Fi22Cls

open CFSG.KC.Enum CFSG.KC.Fi22S0

@[expose] noncomputable def labC (pp pj : Nat → Nat) (lt : Nat → Nat → Nat)
    (W CI REP KW KC : Nat → Nat) (r0 n nc a : Nat) : Bool :=
  strictB (CI a) fun c => bIf(Nat.blt c nc,
    strictB (W a) fun w => bAnd(Nat.blt w n,
      Nat.beq (tm pp pj lt w a) (tm pp pj lt (REP c) w)),
    bAnd(Nat.beq (KW a) (nat_lit 0), bAnd(Nat.beq (KC a) (nat_lit 0),
      bIf(Nat.beq a r0, false, true))))

end CFSG.KC.Fi22Cls

end
