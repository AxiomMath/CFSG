module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.LyFiveRel

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ix (T k : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) T k

@[expose] noncomputable def tAt (mul : Nat → Nat → Nat) (A B ONE PAR GEN : Nat) (TT : Nat → Nat)
    (k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), Nat.beq (TT k) ONE,
    bAnd(Nat.blt (ix PAR k) k, bAnd(Nat.blt (ix GEN k) (nat_lit 2),
      Nat.beq (TT k) (mul (nIf(Nat.beq (ix GEN k) (nat_lit 1), B, A)) (TT (ix PAR k))))))

@[expose] noncomputable def relTree (PAR GEN NXT Q k s : Nat) : Bool :=
  (fun t => bAnd(Nat.beq (ix PAR (ix NXT t)) k, bAnd(Nat.beq (ix GEN (ix NXT t)) s,
    bAnd(Bool.not (Nat.beq (ix NXT t) (nat_lit 0)), Nat.beq (ix Q t) (nat_lit 0)))))
    (Nat.add (Nat.mul (nat_lit 2) k) s)

@[expose] noncomputable def relAt (mul : Nat → Nat → Nat) (A B PAR GEN NXT Q : Nat) (TT NF : Nat → Nat)
    (k s : Nat) : Bool :=
  (fun t => bAnd(Nat.blt (ix NXT t) (nat_lit 2880), bAnd(Nat.blt (ix Q t) (nat_lit 3125),
    bIf(relTree PAR GEN NXT Q k s, true,
      Nat.beq (mul (nIf(Nat.beq s (nat_lit 1), B, A)) (TT k)) (mul (TT (ix NXT t)) (NF (ix Q t)))))))
    (Nat.add (Nat.mul (nat_lit 2) k) s)

end CFSG.KC.LyFiveRel

end
