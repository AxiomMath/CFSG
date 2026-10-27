module

public import Certificates.Data.Kernel.SporSch.J1Pt

public section

namespace CFSG.KS.SporSch.J1C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.SporSch.MOC

@[expose] noncomputable def elJ (n w m nw nb : Nat) (LR TR : Nat → Nat) (j x : Nat) : Nat :=
  apL w m (elemT n nw LR TR nb j) x

@[expose] noncomputable def stpC (w m : Nat) (G GI : Nat → Nat) (l : Nat) (f : Nat → Nat)
    (x : Nat) : Nat :=
  pg w m (G l) (f (pg w m (GI l) x))

@[expose] noncomputable def stpM (w m : Nat) (G : Nat → Nat) (l : Nat) (f : Nat → Nat)
    (x : Nat) : Nat :=
  f (pg w m (G l) x)

@[expose] noncomputable def bfsPtK (n w m nw BP nb N : Nat) (LR TR : Nat → Nat)
    (stp : Nat → (Nat → Nat) → Nat → Nat) (ng c : Nat) (J PA LB POS SRT SRI : Nat → Nat)
    (k : Nat) : Bool :=
  bAnd(Nat.blt (J k) N,
  bAnd(bIf(Nat.beq k (nat_lit 0), true,
    bAnd(Nat.blt (PA k) k, bAnd(Nat.blt (LB k) ng,
    bAnd(Nat.beq (POS (Nat.add (Nat.mul (PA k) ng) (LB k))) k,
      bIf(Nat.blt (Nat.succ k) c, lexLtK (PA k) (LB k) (PA (Nat.succ k)) (LB (Nat.succ k)),
        true))))),
  bAnd(allN ng (fun l => strictB (POS (Nat.add (Nat.mul k ng) l)) (fun q =>
    bAnd(Nat.blt q c,
    bAnd(eqB w m BP nb (elJ n w m nw nb LR TR (J q)) (stp l (elJ n w m nw nb LR TR (J k))),
      bIf(Nat.beq q (nat_lit 0), true, bIf(lexLtK k l (PA q) (LB q), false, true)))))),
  strictB (SRT k) (fun t => bAnd(Nat.blt t c, bAnd(Nat.beq (SRI t) k,
    bIf(Nat.blt (Nat.succ k) c, Nat.blt (J t) (J (SRT (Nat.succ k))), true)))))))

@[expose] noncomputable def bfsPtG (n w m nw BP nb N : Nat) (LR TR : Nat → Nat)
    (stp : Nat → (Nat → Nat) → Nat → Nat) (ng c : Nat) (J PA LB POS SRT SRI : Nat → Nat)
    (k : Nat) : Bool :=
  bIf(Nat.blt k c, bfsPtK n w m nw BP nb N LR TR stp ng c J PA LB POS SRT SRI k, true)

@[expose] noncomputable def bfsHdK (c cap jR : Nat) (J PA LB : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble c cap, bAnd(Nat.beq (J (nat_lit 0)) jR,
    bAnd(Nat.beq (PA (nat_lit 0)) (nat_lit 0), Nat.beq (LB (nat_lit 0)) (nat_lit 0)))))

@[expose] noncomputable def prodPtK (ng c : Nat) (PA LB POS PT INV : Nat → Nat) (a : Nat) :
    Bool :=
  bAnd(allN c (fun b => strictB (PT (Nat.add (Nat.mul a c) b)) (fun v => bAnd(Nat.blt v c,
    bIf(Nat.beq b (nat_lit 0), Nat.beq v a,
      Nat.beq v (POS (Nat.add (Nat.mul (PT (Nat.add (Nat.mul a c) (PA b))) ng) (LB b))))))),
  bAnd(Nat.blt (INV a) c, Nat.beq (PT (Nat.add (Nat.mul a c) (INV a))) (nat_lit 0)))

@[expose] noncomputable def prodPtG (ng c : Nat) (PA LB POS PT INV : Nat → Nat) (a : Nat) : Bool :=
  bIf(Nat.blt a c, prodPtK ng c PA LB POS PT INV a, true)

@[expose] noncomputable def cjK (c : Nat) (PT INV : Nat → Nat) (a i : Nat) : Nat :=
  PT (Nat.add (Nat.mul (PT (Nat.add (Nat.mul a c) i)) c) (INV a))

@[expose] noncomputable def elK (n w m nw nb : Nat) (LR TR K : Nat → Nat) (k x : Nat) : Nat :=
  apL w m (elemT n nw LR TR nb (K k)) x

@[expose] noncomputable def invB (w m BP nb : Nat) (f g : Nat → Nat) : Bool :=
  fixB w m BP nb (fun x => f (g x))

@[expose] noncomputable def movB (w m BP nb mo : Nat) (f : Nat → Nat) : Bool :=
  bIf(fixB w m BP nb (itF f mo), false, true)

@[expose] noncomputable def oddW2 (w m BP nb mo cK : Nat) (e : Nat → Nat → Nat)
    (W3 W4 : Nat → Nat) (k h hi : Nat) : Bool :=
  strictB (Nat.pred (W3 k)) (fun h2 => strictB (W4 k) (fun i2 =>
    bAnd(Nat.blt h2 cK, bAnd(Nat.blt i2 cK, bAnd(invB w m BP nb (e h2) (e i2),
      movB w m BP nb mo (fun x => e k (e h (e k (e hi (e h2 (e k (e i2 x))))))))))))

@[expose] noncomputable def oddPtK (w m BP nb mo cK : Nat) (e : Nat → Nat → Nat)
    (W1 W2 W3 W4 : Nat → Nat) (k : Nat) : Bool :=
  bIf(fixB w m BP nb (e k), true, bIf(fixB w m BP nb (itF (e k) mo),
    strictB (Nat.pred (W1 k)) (fun h => strictB (W2 k) (fun hi =>
      bAnd(Nat.blt (nat_lit 0) (W1 k), bAnd(Nat.blt h cK, bAnd(Nat.blt hi cK,
      bAnd(invB w m BP nb (e h) (e hi),
      bIf(Nat.beq (W3 k) (nat_lit 0),
        movB w m BP nb mo (fun x => e k (e h (e k (e hi x)))),
        oddW2 w m BP nb mo cK e W3 W4 k h hi))))))),
    true))

@[expose] noncomputable def centPtK (n w m nw BP nb N mo : Nat) (LR TR : Nat → Nat) (R : List Nat)
    (K W1 W2 W3 W4 : Nat → Nat) (cK k : Nat) : Bool :=
  bIf(Nat.blt k cK, bAnd(Nat.blt (K k) N,
    bAnd(bIf(Nat.blt (Nat.succ k) cK, Nat.blt (K k) (K (Nat.succ k)), true),
    bAnd(eqB w m BP nb (fun x => apL w m R (elK n w m nw nb LR TR K k x))
      (fun x => elK n w m nw nb LR TR K k (apL w m R x)),
    oddPtK w m BP nb mo cK (elK n w m nw nb LR TR K) W1 W2 W3 W4 k))), true)

@[expose] noncomputable def ltrK (P PI : Nat → Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => P (Nat.sub k (nat_lit 1))) (fun k => PI k) l

@[expose] noncomputable def wordP (n w m idn : Nat) (L : Int → Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn (fun l _ acc => pcomp n w m (L l) acc) wd

end CFSG.KS.SporSch.J1C

end
