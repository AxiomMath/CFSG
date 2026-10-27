module

public import Certificates.Data.Kernel.Fi22Twist.Search

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def tfK (T TT S : Nat → Nat) (f : Nat) : Bool :=
  strictB (TT f) fun r =>
  strictB (T f) fun t =>
  bIf(Nat.beq (fld(r, nat_lit 8, nat_lit 65535)) (nat_lit 0),
    allN (nat_lit 3510) (fun i => Nat.beq (ap t i) i),
    bAnd(Nat.blt (fld(r, nat_lit 24, nat_lit 65535)) f,
      bAnd(Nat.blt (Nat.shiftRight r (nat_lit 40)) (nat_lit 19),
        strictB (S (Nat.shiftRight r (nat_lit 40))) fun s =>
        strictB (T (fld(r, nat_lit 24, nat_lit 65535))) fun u =>
        allN (nat_lit 3510) (fun i => Nat.beq (ap t i) (ap s (ap u i))))))

end CFSG.KC.Fi22Twist

end
