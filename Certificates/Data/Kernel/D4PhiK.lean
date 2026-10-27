module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.D4Phi

open CFSG.KC.Enum (pg allN eq22)
open CFSG.KS (mask)
open CFSG.KC.Misc.ArrEnum (permB)

@[expose] noncomputable def sqK (c : Nat) : Nat :=
  Nat.land (Nat.shiftRight (nat_lit 846615568) (Nat.mul (nat_lit 4) c)) (nat_lit 15)

@[expose] noncomputable def sgK (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 8), sqK k,
    nIf(Nat.blt k (nat_lit 16), Nat.add (nat_lit 8) (sqK (Nat.sub k (nat_lit 8))), k))

@[expose] noncomputable def frobAt (V W : Nat) : Bool :=
  allN (nat_lit 8) fun j => Nat.beq (pg (nat_lit 3) (mask (nat_lit 3)) W j)
    (sqK (pg (nat_lit 3) (mask (nat_lit 3)) V j))

@[expose] noncomputable def phiK (F : Nat) (LV LP : Nat → Nat) : Bool :=
  bAnd(permB (nat_lit 2457) (nat_lit 12) F,
    bAnd(allN (nat_lit 2457) (fun i => frobAt (LV i) (LV (pg (nat_lit 12) (mask (nat_lit 12)) F i))),
      bAnd(allN (nat_lit 2457) (fun i => Nat.beq (pg (nat_lit 12) (mask (nat_lit 12)) F
          (pg (nat_lit 12) (mask (nat_lit 12)) F (pg (nat_lit 12) (mask (nat_lit 12)) F i))) i),
        allN (nat_lit 18) fun k =>
          eq22 (nat_lit 2457) (nat_lit 12) (mask (nat_lit 12)) F (LP k) (LP (sgK k)) F)))

end CFSG.KC.D4Phi

end
