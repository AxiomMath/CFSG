module

public import Certificates.Data.Kernel.McLAS.Pair
public import Certificates.Data.Kernel.Spor.Mathieu
public import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KS.McLNine

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.McLAS CFSG.KS.Mathieu

@[expose] noncomputable def ltK (F : Nat → Nat) (l : Nat) : Nat := F (Nat.add l (nat_lit 4))

@[expose] noncomputable def wK (F : Nat → Nat) (wd : List Nat) : Nat :=
  wordTabK (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) idK (ltK F) wd

@[expose] noncomputable def walkK (F : Nat → Nat) (wd : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p
    (fun l _ ih => strictN ih (fun q => pg (nat_lit 9) (mask (nat_lit 9)) (ltK F l) q)) wd

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (pcK a b) (pcK b a)

@[expose] noncomputable def wordsK (F G : Nat → Nat) (ws : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih i => bAnd(Nat.beq (wK F w) (G i), ih (Nat.succ i))) ws

@[expose] noncomputable def walksK (F : Nat → Nat) (p : Nat) (os : List (List Nat)) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun pts => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) pts)
    (fun w _ ih pts => List.rec (motive := fun _ => Bool) false
      (fun q qs _ => bAnd(Nat.beq (walkK F w p) q, ih qs)) pts) os

@[expose] noncomputable def sortedK (pts : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => bAnd(List.rec (motive := fun _ => Bool) true (fun y _ _ => Nat.blt x y) xs, ih))
    pts

@[expose] noncomputable def cntK (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => nIf(f i, Nat.succ ih, ih)) n

@[expose] noncomputable def cwK (G : Nat → Nat) (t c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 3), allN (nat_lit 3) (fun j => commK t (G j)),
    bAnd(Nat.blt c (nat_lit 3), bIf(commK t (G c), false, true)))

@[expose] noncomputable def genK (F G : Nat → Nat) (p : Nat) : Bool :=
  allN (nat_lit 3) (fun j => bAnd(Nat.beq (pg (nat_lit 9) (mask (nat_lit 9)) (G j) p) p,
    commK (G j) (F (nat_lit 4))))

@[expose] noncomputable def movK (G : Nat → Nat) (p : Nat) : Bool :=
  allN (nat_lit 275) (fun q => bIf(Nat.beq q p, true,
    bIf(allN (nat_lit 3) (fun j => Nat.beq (pg (nat_lit 9) (mask (nat_lit 9)) (G j) q) q),
      false, true)))

@[expose] noncomputable def xyK (F : Nat → Nat) (p x y : Nat) : Bool :=
  bAnd(Nat.beq (pg (nat_lit 9) (mask (nat_lit 9)) x p) p,
  bAnd(Nat.beq (pg (nat_lit 9) (mask (nat_lit 9)) y p) p,
  bAnd(commK x (F (nat_lit 4)), bAnd(commK y (F (nat_lit 4)),
  bAnd(Nat.beq (pwK (nat_lit 3) x) idK, bAnd(Nat.beq (pwK (nat_lit 3) y) idK,
  bAnd(commK x y, bAnd(bIf(Nat.beq x idK, false, true),
  bAnd(bIf(Nat.beq y idK, false, true), bAnd(bIf(Nat.beq y x, false, true),
    bIf(Nat.beq y (pcK x x), false, true)))))))))))

@[expose] noncomputable def mcl9K (F G T PL POS SRT SRI : Nat → Nat) (cnt : Nat) (CW : List Nat)
    (ws : List (List Nat)) (wx wy : List Nat) (p : Nat) (os : List (List Nat)) (pts : List Nat) :
    Bool :=
  bAnd(wordsK F G ws (nat_lit 0),
  bAnd(Nat.beq cnt (nat_lit 128), bAnd(penumHdK idK cnt (nat_lit 128) T PL,
  bAnd(penumSlK (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) (Nat.mul (nat_lit 275) (nat_lit 9))
    false G G (nat_lit 3) cnt T PL POS SRT SRI (nat_lit 0) cnt,
  bAnd(allN cnt (fun i => cwK G (T i) (nget CW i)),
  bAnd(Nat.beq (cntK cnt (fun i => Nat.beq (nget CW i) (nat_lit 3))) (nat_lit 2),
  bAnd(genK F G p, bAnd(movK G p,
  bAnd(strictB (wK F wx) (fun x => strictB (wK F wy) (fun y => xyK F p x y)),
  bAnd(walksK F p os pts, sortedK pts))))))))))

end CFSG.KS.McLNine

end
