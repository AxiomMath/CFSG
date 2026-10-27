module

public import Certificates.Data.Kernel.Misc.RuScan

public section

namespace CFSG.KC.Misc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan

@[expose] noncomputable def bX (X : Nat) : Nat :=
  nIf(Nat.beq X (nat_lit 0), nat_lit 0, nIf(Nat.beq X (nat_lit 1), nat_lit 3,
    nIf(Nat.beq X (nat_lit 2), nat_lit 9, nIf(Nat.beq X (nat_lit 4), nat_lit 16, nat_lit 12))))

@[expose] noncomputable def orbM (LR TR : Nat → Nat) (v : Nat) : Nat :=
  strictN (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictN (roff (nat_lit 4060) (nat_lit 48720) (LR 2)) (fun o2 =>
  strictN (rcnt (LR 2)) (fun c2 =>
  strictN (apP v (nat_lit 0)) (fun x =>
  foldN (Nat.mul (rcnt (LR 1)) c2) (fun j acc =>
    Nat.lor acc (Nat.shiftLeft (nat_lit 1) (yAp [TR (Nat.add o1 (Nat.div j c2)),
      TR (Nat.add o2 (Nat.mod j c2))] x))) (nat_lit 0)))))

@[expose] noncomputable def notIn (m r : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m r) (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def l0OK (LR TR R L : Nat → Nat) (i : Nat) : Bool :=
  strictB (TR (Nat.add (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) i)) (fun t =>
  strictB (apP t (nat_lit 0)) (fun q =>
  strictB (Nat.mul (nat_lit 21) i) (fun b =>
  bAnd(allN (nat_lit 5) (fun X => strictB (L (Nat.add b X)) (fun rec =>
      bIf(Nat.beq rec (nat_lit 1), true,
        strictB (R (Nat.add (bX X) fld(rec, nat_lit 1, nat_lit 15))) (fun v =>
        strictB (Nat.shiftRight rec (nat_lit 5)) (fun r =>
          bAnd(Nat.blt r (nat_lit 4060), bAnd(Nat.beq (apP t r) (apP v q),
            notIn (orbM LR TR v) r))))))),
    strictB (L (Nat.add b (nat_lit 5))) (fun rec =>
      bIf(Nat.beq rec (nat_lit 1), true,
        strictB (orbM LR TR (R (Nat.add (nat_lit 12) fld(rec, nat_lit 1, nat_lit 15)))) (fun m =>
        allN (nat_lit 16) (fun w =>
          strictB (Nat.shiftRight (L (Nat.add (Nat.add b (nat_lit 5)) w)) (nat_lit 5)) (fun r =>
            bAnd(Nat.blt r (nat_lit 4060), bAnd(Nat.beq (apP t r) (apP (R (Nat.add (nat_lit 21) w)) q),
              notIn m r)))))))))))

@[expose] noncomputable def l0Chk (LR TR R L : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt (fun d => l0OK LR TR R L (Nat.add lo d))

end CFSG.KC.Misc.RuBigZ

end
