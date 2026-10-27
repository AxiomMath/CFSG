module

public import Certificates.Data.Kernel.BalanceSC.Sylow

public section

namespace CFSG.KC.Gen6125

open CFSG.KC.Enum (pg pcomp pidn strictB)
open CFSG.KC.LQT.P (allN)
open CFSG.KC.BalanceSC (getL allL memL isoK commK movK eightSubK)
open CFSG.KC.Misc.ArrEnum (permB)

@[expose] noncomputable def atK (n N : Nat) (PT : Nat → Nat) (jmode : Bool)
    (GG IA IB IC : List Nat) (e j : Nat) : Bool :=
  strictB (getL (nat_lit 0) GG j) fun g => strictB (PT (getL (nat_lit 0) IA j)) fun a =>
    bAnd(Nat.blt (getL (nat_lit 0) IA j) N, bAnd(permB n (nat_lit 4) g,
      bAnd(isoK n e a, bAnd(commK n a g,
        bIf(jmode,
          strictB (PT (getL (nat_lit 0) IB j)) fun b => strictB (PT (getL (nat_lit 0) IC j)) fun c =>
            strictB (pcomp n (nat_lit 4) (nat_lit 15) a b) fun ab =>
              bAnd(Nat.blt (getL (nat_lit 0) IB j) N, bAnd(Nat.blt (getL (nat_lit 0) IC j) N,
                bAnd(isoK n e b, bAnd(isoK n e c, bAnd(isoK n e ab,
                  bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) a c),
                    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) b c),
                      bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) ab c),
                        eightSubK n e a b c ab)))))))),
          true)))))

@[expose] noncomputable def atsK (n N : Nat) (PT : Nat → Nat) (jmode : Bool)
    (GG IA IB IC : List Nat) : Bool :=
  strictB (pidn n (nat_lit 4)) fun e => allN (nat_lit 3) fun j => atK n N PT jmode GG IA IB IC e j

@[expose] noncomputable def wordP (n : Nat) (GG : List Nat) (w : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun t => t)
    (fun j _ ih t => ih (pcomp n (nat_lit 4) (nat_lit 15) t (getL (nat_lit 0) GG j))) w t

@[expose] noncomputable def wordK (n : Nat) (GG w : List Nat) : Bool :=
  bAnd(allL w fun j => Nat.blt j (nat_lit 3),
    Nat.beq (movK n (wordP n GG w (pidn n (nat_lit 4)))) (nat_lit 3))

@[expose] noncomputable def stepK (GG OC OP OL : List Nat) (k : Nat) : Bool :=
  strictB (getL (nat_lit 0) OC (getL (nat_lit 0) OP k)) fun c =>
    strictB (getL (nat_lit 0) GG (getL (nat_lit 0) OL k)) fun g =>
      bAnd(Nat.blt (getL (nat_lit 0) OP k) k, bAnd(Nat.blt (getL (nat_lit 0) OL k) (nat_lit 3),
        Nat.beq (getL (nat_lit 0) OC k)
          (Nat.add (pg (nat_lit 4) (nat_lit 15) g (Nat.mod c (nat_lit 16)))
            (Nat.mul (nat_lit 16) (pg (nat_lit 4) (nat_lit 15) g (Nat.div c (nat_lit 16)))))))

@[expose] noncomputable def pairK (n : Nat) (GG OC OP OL : List Nat) : Bool :=
  bAnd(Nat.beq (getL (nat_lit 0) OC (nat_lit 0)) (nat_lit 16),
    bAnd(strictB OC.length fun m =>
        allN m fun k => bIf(Nat.beq k (nat_lit 0), true, stepK GG OC OP OL k),
      allN n fun x => allN n fun y =>
        bIf(Nat.beq x y, true, memL (Nat.add x (Nat.mul (nat_lit 16) y)) OC)))

end CFSG.KC.Gen6125

end
