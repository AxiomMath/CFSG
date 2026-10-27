module

public import Certificates.Data.Kernel.Spor.PSearch
public import Certificates.Data.Kernel.Spor.RebuildK
public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KS.HypK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PSearch CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def dg3 (k t : Nat) : Nat :=
  Nat.mod (Nat.div k (Nat.pow (nat_lit 3) t)) (nat_lit 3)

@[expose] noncomputable def dot5 (a b : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (dg3 a 0) (dg3 b 0)) (Nat.add (Nat.mul (dg3 a 1) (dg3 b 1))
    (Nat.add (Nat.mul (dg3 a 2) (dg3 b 2)) (Nat.add (Nat.mul (dg3 a 3) (dg3 b 3))
      (Nat.mul (dg3 a 4) (dg3 b 4)))))) (nat_lit 3)

@[expose] noncomputable def actC (M : List Nat) (k t : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (dg3 k 0) (dg3 (nthN M 0) t)) (Nat.add (Nat.mul (dg3 k 1) (dg3 (nthN M 1) t))
    (Nat.add (Nat.mul (dg3 k 2) (dg3 (nthN M 2) t)) (Nat.add (Nat.mul (dg3 k 3) (dg3 (nthN M 3) t))
      (Nat.mul (dg3 k 4) (dg3 (nthN M 4) t)))))) (nat_lit 3)

@[expose] noncomputable def act5 (M : List Nat) (k : Nat) : Nat :=
  Nat.add (actC M k 0) (Nat.mul (nat_lit 3) (Nat.add (actC M k 1) (Nat.mul (nat_lit 3)
    (Nat.add (actC M k 2) (Nat.mul (nat_lit 3) (Nat.add (actC M k 3)
      (Nat.mul (nat_lit 3) (actC M k 4))))))))

@[expose] noncomputable def dbl5 (k : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.mul 2 (dg3 k 0)) 3) (Nat.mul (nat_lit 3) (Nat.add (Nat.mod (Nat.mul 2 (dg3 k 1)) 3)
    (Nat.mul (nat_lit 3) (Nat.add (Nat.mod (Nat.mul 2 (dg3 k 2)) 3) (Nat.mul (nat_lit 3)
      (Nat.add (Nat.mod (Nat.mul 2 (dg3 k 3)) 3) (Nat.mul (nat_lit 3) (Nat.mod (Nat.mul 2 (dg3 k 4)) 3))))))))

@[expose] noncomputable def lead5 (k : Nat) : Nat :=
  nIf(Nat.beq (dg3 k 0) 0, nIf(Nat.beq (dg3 k 1) 0, nIf(Nat.beq (dg3 k 2) 0,
    nIf(Nat.beq (dg3 k 3) 0, dg3 k 4, dg3 k 3), dg3 k 2), dg3 k 1), dg3 k 0)

@[expose] noncomputable def canon5 (k : Nat) : Nat := nIf(Nat.beq (lead5 k) 1, k, dbl5 k)

@[expose] noncomputable def mapsTo (M : List Nat) (p m : Nat) : Bool :=
  allN 243 fun k => bIf(Nat.beq (dot5 p k) 0, Nat.beq (dot5 m (act5 M k)) 0, true)

@[expose] noncomputable def memN (l : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a x, true, ih)) l

@[expose] noncomputable def memR (fr : List (List Nat)) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq (nthN a 0) x, true, ih)) fr

@[expose] noncomputable def normB (m : Nat) : Bool :=
  bAnd(Nat.blt 0 m, bAnd(Nat.blt m 243, Nat.beq (canon5 m) m))

@[expose] noncomputable def rowOK (hm : List Nat) (Ms : List (List Nat)) (seen row : List Nat) :
    Bool :=
  bAnd(normB (nthN row 0), bIf(Nat.beq (nthN row 2) 2,
    bAnd(Nat.beq (nthN row 1) (nthN row 0), memN hm (nthN row 0)),
    bAnd(Nat.blt (nthN row 2) 2, bAnd(memN seen (nthN row 1),
      mapsTo (nthL Ms (nthN row 2)) (nthN row 1) (nthN row 0)))))

@[expose] noncomputable def rowsOK (hm : List Nat) (Ms : List (List Nat)) (fr : List (List Nat)) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun row _ ih seen => bAnd(rowOK hm Ms seen row, ih (nthN row 0 :: seen))) fr

@[expose] noncomputable def frOK (hm : List Nat) (Ms : List (List Nat)) (fr : List (List Nat)) :
    Bool :=
  bAnd(rowsOK hm Ms fr [], allN 243 fun x => bIf(Nat.beq x 0, true, memR fr (canon5 x)))

@[expose] noncomputable def inPK (n w : Nat) (LR TRI : Nat → Nat) (BP g : Nat) : Bool :=
  bAnd(permB n w g, siftK n w (mask w) (Nat.mul n w) (pidn n w) LR TRI BP 6 0 g)

@[expose] noncomputable def mulD (n w d a x : Nat) : Nat :=
  nIf(Nat.beq a 0, x, nIf(Nat.beq a 1, pcomp n w (mask w) d x,
    strictN (pcomp n w (mask w) d x) (pcomp n w (mask w) d)))

@[expose] noncomputable def ePg (n w : Nat) (D : List Nat) (k x : Nat) : Nat :=
  strictN (mulD n w (nthN D 4) (dg3 k 4) x) fun x4 =>
  strictN (mulD n w (nthN D 3) (dg3 k 3) x4) fun x3 =>
  strictN (mulD n w (nthN D 2) (dg3 k 2) x3) fun x2 =>
  strictN (mulD n w (nthN D 1) (dg3 k 1) x2) fun x1 =>
  mulD n w (nthN D 0) (dg3 k 0) x1

@[expose] noncomputable def dOK (n w : Nat) (LR TRI : Nat → Nat) (BP : Nat) (D : List Nat) : Bool :=
  allN 5 fun i => strictB (nthN D i) fun d => bAnd(inPK n w LR TRI BP d,
    bAnd(Nat.beq (pcomp n w (mask w) d (pcomp n w (mask w) d d)) (pidn n w),
      allN 5 fun j => strictB (nthN D j) fun e =>
        Nat.beq (pcomp n w (mask w) d e) (pcomp n w (mask w) e d)))

@[expose] noncomputable def withReb (n w : Nat) (LR TR TRI : Nat → Nat) (β : List Nat)
    (f : Nat → Bool → Bool) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun g r => Prod.rec (motive := fun _ => Bool)
      (fun _ ok => strictB g fun g => f g ok) r)
    (rebK n w LR TR TRI (fun l => nthN β l) 6)

@[expose] noncomputable def nOK (n w : Nat) (LR TR TRI : Nat → Nat) (BP : Nat) (D : List Nat)
    (nb M : List (List Nat)) : Bool :=
  allN 2 fun i => withReb n w LR TR TRI (nthL nb i) fun q ok =>
    bAnd(ok, bAnd(inPK n w LR TRI BP q,
      allN 5 fun l => Nat.beq (pcomp n w (mask w) q (nthN D l)) (ePg n w D (nthN (nthL M i) l) q)))

@[expose] noncomputable def bindOK (n w : Nat) (LR TR TRI : Nat → Nat) (BP : Nat) (D gb ks Ys : List Nat) :
    Bool :=
  withReb n w LR TR TRI gb fun g ok => bAnd(ok, bAnd(inPK n w LR TRI BP g,
    allN 10 fun t => strictB (nthN Ys t) fun Y => bAnd(permB n w Y,
      Nat.beq (pcomp n w (mask w) g Y) (ePg n w D (nthN ks t) g))))

@[expose] noncomputable def orthOK (m : Nat) (ks : List Nat) : Bool :=
  bAnd(normB m, allN 10 fun t => bAnd(Nat.blt (nthN ks t) 243, Nat.beq (dot5 m (nthN ks t)) 0))

@[expose] noncomputable def searchOK (n w : Nat) (LR TR TRI : Nat → Nat) (BP : Nat) (src Yl Yp : List Nat) :
    Bool :=
  bAnd(srcOK w (mask w) BP 6 src Yl,
    Nat.ble (pcnt n w (mask w) (Nat.mul n w) LR TR TRI BP 6 src Yl Yp) 243)

end CFSG.KS.HypK

end
