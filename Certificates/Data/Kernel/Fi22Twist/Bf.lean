module

public import Certificates.Data.Kernel.Fi22Twist.Search

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def bfK (BF S : Nat → Nat) (k : Nat) : Bool :=
  strictB (BF k) fun r =>
  bIf(Nat.beq k (nat_lit 0),
    bAnd(Nat.beq (fld(r, nat_lit 0, nat_lit 4095)) (nat_lit 3),
      Nat.beq (fld(r, nat_lit 12, nat_lit 4095)) (nat_lit 6)),
    bAnd(Nat.blt (fld(r, nat_lit 108, nat_lit 4095)) k,
      bAnd(Nat.blt (Nat.shiftRight r (nat_lit 120)) (nat_lit 19),
        strictB (S (Nat.shiftRight r (nat_lit 120))) fun s =>
        strictB (BF (fld(r, nat_lit 108, nat_lit 4095))) fun q =>
        bAnd(allBlk (nat_lit 0) (fun m => Nat.beq (ap s (bp m)) (bp m)) (nat_lit 3),
          allBlk (nat_lit 0) (fun p => Nat.beq (fld(r, Nat.mul (nat_lit 12) p, nat_lit 4095))
            (ap s (fld(q, Nat.mul (nat_lit 12) p, nat_lit 4095)))) (nat_lit 9)))))

end CFSG.KC.Fi22Twist

end
