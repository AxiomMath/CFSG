module

public import Certificates.Data.Kernel.FixBoundK.Member
public import Certificates.Data.Kernel.SortTree

public section

namespace CFSG.KC.FixBoundK.Pair

open CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.FixBoundK

@[expose] noncomputable def ap (X p : Nat) : Nat := fget X p (nat_lit 5)

@[expose] noncomputable def ivc (IV i : Nat) : Nat := fget IV i (nat_lit 120)

@[expose] noncomputable def rk (R : Nat) : Nat := fget R (nat_lit 0) (nat_lit 8)

@[expose] noncomputable def gI (R j : Nat) : Nat := fget R (Nat.succ j) (nat_lit 8)

@[expose] noncomputable def idc : Nat :=
  orN (nat_lit 24) fun i => Nat.shiftLeft i (Nat.mul (nat_lit 5) i)

@[expose] noncomputable def pA (IV R μ p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun j ih p => ih (nIf(bit μ j, ap (ivc IV (gI R j)) p, p))) (nat_lit 6) p

@[expose] noncomputable def allB (BP nB : Nat) (f : Nat → Bool) : Bool :=
  allN nB fun k => f (fget BP k (nat_lit 5))

@[expose] noncomputable def anyB (BP nB : Nat) (f : Nat → Bool) : Bool :=
  anyN nB fun k => f (fget BP k (nat_lit 5))

@[expose] noncomputable def invOK (IV IR : Nat) (rec : Nat → Nat) (n i : Nat) : Bool :=
  strictK (ivc IV i) fun X =>
    bAnd(Nat.beq X (valF (nat_lit 120) (rec (fget IR i (nat_lit 10)))),
    bAnd(allN (nat_lit 24) (fun p => Nat.beq (ap X (ap X p)) p),
    bAnd(notB (Nat.beq X idc),
      bIf(Nat.blt (Nat.succ i) n,
        Nat.blt (fget IR i (nat_lit 10)) (fget IR (Nat.succ i) (nat_lit 10)), true))))

@[expose] noncomputable def baseOK (BP nB : Nat) (rec : Nat → Nat) (j : Nat) : Bool :=
  strictK (valF (nat_lit 120) (rec j)) fun X =>
    orB (notB (allB BP nB fun β => Nat.beq (ap X β) β)) (Nat.beq X idc)

@[expose] noncomputable def commB (BP nB X Y : Nat) : Bool :=
  allB BP nB fun β => Nat.beq (ap X (ap Y β)) (ap Y (ap X β))

@[expose] noncomputable def cmOK (IV CM BP nB n a : Nat) : Bool :=
  strictK (ivc IV a) fun A => strictK (fget CM a n) fun Ra =>
    allN n fun b => orB (bit Ra b) (strictK (ivc IV b) fun X => notB (commB BP nB A X))

@[expose] noncomputable def eqDec (X : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 24))
    (fun v _ ih i => bAnd(Nat.beq (ap X i) v, ih (Nat.succ i))) l (nat_lit 0)

@[expose] noncomputable def gensOK (IV R n : Nat) (gl : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (rk R))
    (fun g _ ih j => bAnd(Nat.blt (gI R j) n, bAnd(eqDec (ivc IV (gI R j)) g, ih (Nat.succ j))))
    gl (nat_lit 0)

@[expose] noncomputable def repOK (IV RG BP nB n t r : Nat) (gl : List (List Nat)) : Bool :=
  strictK (fget RG t (nat_lit 56)) fun R =>
    bAnd(Nat.beq (rk R) r,
    bAnd(gensOK IV R n gl,
    bAnd(allN r (fun i => allN i fun j =>
        strictK (ivc IV (gI R i)) fun A => strictK (ivc IV (gI R j)) fun X => commB BP nB A X),
      allN (Nat.sub (pw2 r) (nat_lit 1)) fun μ =>
        anyB BP nB fun β => notB (Nat.beq (pA IV R (Nat.succ μ) β) β))))

@[expose] noncomputable def xorSel (mp s m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => Nat.xor (nIf(bit s j, fget mp j (nat_lit 6), nat_lit 0)) ih) m

abbrev Item := Nat × Nat × Nat × Nat × Nat

@[expose] noncomputable def pairK (IV BP nB R r x R' G cp mp sp : Nat) : Bool :=
  bAnd(Nat.beq (rk R') (Nat.succ r),
  bAnd(allN nB (fun k => Nat.beq (ap G (fget cp k (nat_lit 5))) (fget BP k (nat_lit 5))),
  bAnd(allN (Nat.succ r) (fun i =>
      strictK (nIf(Nat.blt i r, ivc IV (gI R i), x)) fun y =>
        strictK (fget mp i (nat_lit 6)) fun μ =>
          bAnd(Nat.blt μ (pw2 (Nat.succ r)),
            allN nB fun k => Nat.beq (ap G (ap y (fget cp k (nat_lit 5))))
              (pA IV R' μ (fget BP k (nat_lit 5))))),
    allN (Nat.succ r) fun i => Nat.beq (xorSel mp (fget sp i (nat_lit 6)) (Nat.succ r)) (pw2 i))))

@[expose] noncomputable def itemOK (IV RG BP nB nE nR : Nat) (rec : Nat → Nat) (R r x : Nat)
    (it : Item) : Bool :=
  bIf(Nat.beq it.1 (nat_lit 0),
    bAnd(Nat.blt it.2.1 (pw2 r), allB BP nB fun β => Nat.beq (ap x β) (pA IV R it.2.1 β)),
    bAnd(Nat.ble it.1 nR, bAnd(Nat.blt it.2.1 nE,
      strictK (fget RG (Nat.sub it.1 (nat_lit 1)) (nat_lit 56)) fun R' =>
        strictK (valF (nat_lit 120) (rec it.2.1)) fun G =>
          pairK IV BP nB R r x R' G it.2.2.1 it.2.2.2.1 it.2.2.2.2)))

@[expose] noncomputable def walk (IV RG BP nB nE nR : Nat) (rec : Nat → Nat) (R r Cm n : Nat) :
    Nat → List Item → Bool :=
  Nat.rec (motive := fun _ => Nat → List Item → Bool)
    (fun _ l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun _ ih b l => bIf(bit Cm b,
      List.rec (motive := fun _ => Bool) false
        (fun it rest _ => bAnd(strictK (ivc IV b) fun x => itemOK IV RG BP nB nE nR rec R r x it,
          ih (Nat.succ b) rest)) l,
      ih (Nat.succ b) l)) n

@[expose] noncomputable def srcOK (IV RG CM BP nB nE nR n : Nat) (rec : Nat → Nat) (s : Nat)
    (items : List Item) : Bool :=
  bAnd(Nat.ble s nR,
    strictK (nIf(Nat.beq s (nat_lit 0), nat_lit 0, fget RG (Nat.sub s (nat_lit 1)) (nat_lit 56)))
      fun R => strictK (rk R) fun r =>
        strictK (Nat.rec (motive := fun _ => Nat) (Nat.sub (pw2 n) (nat_lit 1))
            (fun j ih => Nat.land (fget CM (gI R j) n) ih) r) fun Cm =>
          walk IV RG BP nB nE nR rec R r Cm n (nat_lit 0) items)

@[expose] noncomputable def srcAt (IV RG CM BP nB nE nR n : Nat) (rec : Nat → Nat) (lo : Nat)
    (src : List (Nat × List Item)) (i : Nat) : Bool :=
  (fun e : Nat × List Item => bAnd(Nat.beq e.1 (Nat.add lo i),
      srcOK IV RG CM BP nB nE nR n rec e.1 e.2))
    (nthS (nat_lit 0, []) src i)

@[expose] noncomputable def repAtP (IV RG BP nB n lo : Nat) (reps : List Rep)
    (gens : List (List (List Nat))) (i : Nat) : Bool :=
  repOK IV RG BP nB n (Nat.add lo i) (nthS repD reps i).1 (nthS [] gens i)

end CFSG.KC.FixBoundK.Pair

end
