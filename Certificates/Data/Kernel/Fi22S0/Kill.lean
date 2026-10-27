module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi22S0

open CFSG.KC.Enum

@[expose] noncomputable def tmF (pp pj : Nat → Nat) (lt : Nat → Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ b => b)
    (fun _ ih a b => strictN (pp a) fun p => nIf(Nat.blt p a, lt (pj a) (ih p b), b))

@[expose] noncomputable def tm (pp pj : Nat → Nat) (lt : Nat → Nat → Nat) (a b : Nat) : Nat :=
  tmF pp pj lt (Nat.succ a) a b

@[expose] noncomputable def killC (pp pj : Nat → Nat) (lt : Nat → Nat → Nat) (W CI REP : Nat → Nat)
    (n nc a : Nat) : Bool :=
  bIf(Nat.beq a (nat_lit 0), true,
    strictB (tm pp pj lt a (tm pp pj lt a a)) fun c => bIf(Nat.beq c (nat_lit 0),
      strictB (W a) fun w => strictB (CI a) fun r => bAnd(Nat.blt w n, bAnd(Nat.blt r nc,
        Nat.beq (tm pp pj lt w a) (tm pp pj lt (REP r) w))), true))

@[expose] noncomputable def repC (pp pj : Nat → Nat) (lt : Nat → Nat → Nat) (REP : Nat → Nat)
    (cw : Nat → Nat → Nat) (n m r : Nat) : Bool :=
  strictB (REP r) fun x => bAnd(Nat.blt x n,
    allN m fun k => strictB (cw r k) fun c => bAnd(Nat.blt c n,
      bAnd(bIf(Nat.beq k (nat_lit 0), true, Nat.blt (cw r (Nat.sub k (nat_lit 1))) c),
        Nat.beq (tm pp pj lt x c) (tm pp pj lt c x))))

end CFSG.KC.Fi22S0

end
