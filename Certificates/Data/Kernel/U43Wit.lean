module

public import Certificates.Data.Kernel.U43Case

public section

namespace CFSG.KC.U43Wit

open CFSG.KC.Enum CFSG.KS CFSG.KC.U43Case

@[expose] noncomputable def cpAt (w t c x : Nat) : Nat :=
  pg w (mask w) t (pg w (mask w) c (pg w (mask w) t x))

@[expose] noncomputable def neB (a b : Nat) : Bool := bIf(Nat.beq a b, false, true)

@[expose] noncomputable def kFailK (n w t c k wk : Nat) : Bool :=
  strictB (Nat.land wk (nat_lit 7)) fun cd => strictB (Nat.shiftRight wk (nat_lit 3)) fun x =>
    bIf(Nat.beq cd (nat_lit 1), Nat.beq k (pidn n w), bAnd(Nat.blt x n,
    bIf(Nat.beq cd (nat_lit 2), neB (pg w (mask w) k (pg w (mask w) k x)) x,
    bIf(Nat.beq cd (nat_lit 3), neB (pg w (mask w) k (cpAt w t c x)) (cpAt w t c (pg w (mask w) k x)),
    bIf(Nat.beq cd (nat_lit 4), neB (pg w (mask w) k (cpAt w t k x)) (cpAt w t k (pg w (mask w) k x)),
    bIf(Nat.beq cd (nat_lit 5),
      neB (pg w (mask w) k (pg w (mask w) c (pg w (mask w) k (pg w (mask w) c x)))) x, false))))))

@[expose] noncomputable def relK (n w t y c e : Nat) : Bool :=
  strictB (Nat.land e (nat_lit 3)) fun a =>
  strictB (Nat.land (Nat.shiftRight e (nat_lit 2)) (nat_lit 3)) fun b =>
  strictB (Nat.land (Nat.shiftRight e (nat_lit 4)) (nat_lit 3)) fun d =>
    bAnd(Nat.blt a (nat_lit 3), bAnd(Nat.blt b (nat_lit 3), bAnd(Nat.blt d (nat_lit 3),
    bAnd(Nat.blt (nat_lit 0) (Nat.add a (Nat.add b d)),
      Nat.beq (pp n w (pp n w (ppw n w y a) (ppw n w c b)) (ppw n w (cpP n w t c) d)) (pidn n w)))))

@[expose] noncomputable def cFailK (n w t y c wc : Nat) (WK : Nat → Nat) (N : Nat) (Y : Nat → Nat) :
    Bool :=
  strictB (Nat.land wc (nat_lit 7)) fun cd => strictB (Nat.shiftRight wc (nat_lit 3)) fun x =>
    bIf(Nat.beq cd (nat_lit 0),
      allN N (fun j => kFailK n w t c (Y j) (Nat.land (Nat.shiftRight (WK j) (Nat.mul (nat_lit 16) x))
        (nat_lit 65535))),
    bIf(Nat.beq cd (nat_lit 1), Nat.beq c (pidn n w),
    bIf(Nat.beq cd (nat_lit 5), relK n w t y c x, bAnd(Nat.blt x n,
    bIf(Nat.beq cd (nat_lit 2),
      neB (pg w (mask w) c (pg w (mask w) c (pg w (mask w) c x))) x,
    bIf(Nat.beq cd (nat_lit 3), neB (pg w (mask w) c (cpAt w t c x)) (cpAt w t c (pg w (mask w) c x)),
    bIf(Nat.beq cd (nat_lit 4), neB (pg w (mask w) y (cpAt w t c x)) (cpAt w t c (pg w (mask w) y x)),
      false)))))))

@[expose] noncomputable def noSolK (n w t y : Nat) (WC WK : Nat → Nat) (N : Nat) (Y : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) fun i =>
    bIf(Nat.blt i N, cFailK n w t y (Y i) (WC i) WK N Y, true))

@[expose] noncomputable def treeK (n w : Nat) (G : Nat → Nat) (nG : Nat) (Y YP YL : Nat → Nat)
    (N lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) fun i =>
    bIf(Nat.blt i N, bIf(Nat.beq i (nat_lit 0), true,
      strictB (YP i) fun p => strictB (YL i) fun l =>
        bAnd(Nat.blt p i, bAnd(Nat.blt l nG, Nat.beq (Y i) (pp n w (G l) (Y p))))), true))

@[expose] noncomputable def sortK (Y SG : Nat → Nat) (N : Nat) : Bool :=
  allN N (fun i => bAnd(Nat.blt (SG i) N,
    bIf(Nat.blt (Nat.succ i) N, Nat.blt (Y (SG i)) (Y (SG (Nat.succ i))), true)))

end CFSG.KC.U43Wit

end
