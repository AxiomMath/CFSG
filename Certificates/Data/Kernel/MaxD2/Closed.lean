module

public import Certificates.Data.Kernel.MaxD2.Check

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def closK (n w cnt : Nat) (T : Nat → Nat) (x xi k h : Nat) : Bool :=
  strictB (pcomp n w (mask w) (pcomp n w (mask w) x (T k)) x) (fun y =>
    bIf(Nat.beq (Nat.land h (nat_lit 1)) (nat_lit 1),
      strictB (Nat.shiftRight h (nat_lit 1)) (fun e => bAnd(Nat.blt e cnt, Nat.beq (T e) y)),
      strictB (Nat.land (Nat.shiftRight h (nat_lit 1)) (nat_lit 65535)) (fun l =>
        strictB (Nat.shiftRight h (nat_lit 17)) (fun e =>
          bAnd(Nat.blt l cnt, bAnd(Nat.blt e cnt,
            Nat.beq (T e) (pcomp n w (mask w) (pcomp n w (mask w) xi (T l)) y)))))))

end CFSG.KS.MaxD2

end
