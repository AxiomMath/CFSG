module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Co1M

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def avK (AP i j : Nat) : Nat := fget AP (Nat.add (Nat.mul (nat_lit 24) i) j) (nat_lit 24)

@[expose] noncomputable def ppg (P i : Nat) : Nat := CFSG.KC.Enum.pg (nat_lit 5) (CFSG.KS.mask (nat_lit 5)) P i

@[expose] noncomputable def ppc (P Q : Nat) : Nat :=
  CFSG.KC.Enum.pcomp (nat_lit 24) (nat_lit 5) (CFSG.KS.mask (nat_lit 5)) P Q

@[expose] noncomputable def symK (AP : Nat) : Bool :=
  allN (nat_lit 24) fun i => allN (nat_lit 24) fun j => Nat.beq (avK AP i j) (avK AP j i)

@[expose] noncomputable def distFK (AP w : Nat) : Bool :=
  allN (nat_lit 24) fun i => allN (nat_lit 24) fun j => bIf(Nat.blt i j,
    strictB (avK AP i j) fun a =>
      allN (nat_lit 24) fun k => allN (nat_lit 24) fun l => bIf(Nat.blt k l,
        bIf(andB (Nat.beq i k) (Nat.beq j l), true,
          strictB (avK AP k l) fun b => andB (notB (Nat.beq a b)) (notB (Nat.beq a (Nat.xor b w)))),
        true),
    true)

@[expose] noncomputable def indK (AP w MT P : Nat) : Bool :=
  andB (Nat.beq (vmF (nat_lit 24) MT w) w)
    (allN (nat_lit 24) fun i => allN (nat_lit 24) fun j => bIf(Nat.blt i j,
      strictB (vmF (nat_lit 24) MT (avK AP i j)) fun v => strictB (avK AP (ppg P i) (ppg P j)) fun u =>
        orB (Nat.beq v u) (Nat.beq v (Nat.xor u w)),
      true))

@[expose] noncomputable def ind1K (AP w MT : Nat) : Bool :=
  andB (Nat.beq (vmF (nat_lit 24) MT w) w)
    (allN (nat_lit 24) fun i => allN (nat_lit 24) fun j => bIf(Nat.blt i j,
      strictB (vmF (nat_lit 24) MT (avK AP i j)) fun v => strictB (avK AP i j) fun u =>
        orB (Nat.beq v u) (Nat.beq v (Nat.xor u w)),
      true))

@[expose] noncomputable def permK (P Pi : Nat) : Bool :=
  allN (nat_lit 24) fun i => andB (Nat.blt (ppg P i) (nat_lit 24)) (andB (Nat.blt (ppg Pi i) (nat_lit 24))
    (andB (Nat.beq (ppg P (ppg Pi i)) i) (Nat.beq (ppg Pi (ppg P i)) i)))

@[expose] noncomputable def pwGo (Ps : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (ppc acc (getL (nat_lit 0) Ps l)) ih) w

@[expose] noncomputable def pwK (Ps : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun l t _ => pwGo Ps t (getL (nat_lit 0) Ps l)) w

@[expose] noncomputable def wK (Ms : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulF (nat_lit 24) acc (getL (nat_lit 0) Ms l)) ih) w (idF (nat_lit 24))

@[expose] noncomputable def actX (H Hi : List Nat) (l t : Nat) : Nat :=
  ppc (ppc (getL (nat_lit 0) H l) t) (getL (nat_lit 0) Hi l)

@[expose] noncomputable def actP (G : List Nat) (l x : Nat) : Nat := ppg (getL (nat_lit 0) G l) x

@[expose] noncomputable def actV (MT : List Nat) (l v : Nat) : Nat := vmF (nat_lit 24) (getL (nat_lit 0) MT l) v

@[expose] noncomputable def actM (U : List Nat) (l X : Nat) : Nat := mulF (nat_lit 24) X (getL (nat_lit 0) U l)

@[expose] noncomputable def conjK (E : List Nat) (s : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => List.cons (mulF (nat_lit 24) (mulF (nat_lit 24) e s) e) ih) (prodsK E (nat_lit 5))

@[expose] noncomputable def invsK (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (Nat.beq (mulF (nat_lit 24) e e) (idF (nat_lit 24))) ih) (prodsK E (nat_lit 5))

@[expose] noncomputable def zipK {α : Type} (f : α → Nat → Bool) (xs : List α) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun ys => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun x _ ih ys => List.rec (motive := fun _ => Bool) false (fun y ys' _ => andB (f x y) (ih ys')) ys) xs

@[expose] noncomputable def ewK (Ms : List Nat) (p : List Nat × Nat) (E : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun w m => Nat.beq (powK (nat_lit 24) (wK Ms w) m) E) p

@[expose] noncomputable def trEqK (M T : Nat) : Bool := Nat.beq (trK (nat_lit 24) M) T

@[expose] noncomputable def uniK (U : Nat) : Bool :=
  allN (nat_lit 24) fun i => strictB (fget U i (nat_lit 24)) fun r =>
    andB (Nat.beq (Nat.land r (Nat.sub (pw2 i) (nat_lit 1))) (nat_lit 0)) (bit r i)

end CFSG.KC.Co1M

end
