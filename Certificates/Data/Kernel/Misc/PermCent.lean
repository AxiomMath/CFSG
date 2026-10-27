module

public import Certificates.Data.Kernel.Misc.PermClosW

public section

namespace CFSG.KC.Misc.Cent

open CFSG.KC.Ord CFSG.KS
open CFSG.KC.Enum (pg)
open CFSG.KC.LQT.P (allN allL anyL letB impB)

@[expose] noncomputable def bitB (M b : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land M (Nat.shiftLeft (nat_lit 1) b))

@[expose] noncomputable def covOK (n w : Nat) (nO : Nat) (R : Nat → Nat) (O : Nat → List Nat)
    (U : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ used => Nat.beq used (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))
    (fun _ ih k used =>
      List.rec (motive := fun _ => Nat → Bool) (fun u => ih (Nat.succ k) u)
        (fun q _ ihl u => andB (Nat.blt q n) (andB (notB (bitB u q))
          (andB (Nat.beq (pg w (mask w) (U q) (R k)) q)
            (ihl (Nat.lor u (Nat.shiftLeft (nat_lit 1) q)))))) (O k) used)
    nO (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def orbOK (n w : Nat) (G : Nat → Nat) (nG : Nat) (R : Nat → Nat)
    (O : Nat → List Nat) (k : Nat) : Bool :=
  andB (Nat.blt (R k) n)
    (allL (O k) fun q => allN nG fun j => anyL (O k) fun q' => Nat.beq (pg w (mask w) (G j) q) q')

@[expose] noncomputable def assignOK (w : Nat) (U : Nat → Nat) (L : List Nat) (t used : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun q _ ih u => letB (pg w (mask w) (U q) t) fun v =>
      andB (notB (bitB u v)) (ih (Nat.lor u (Nat.shiftLeft (nat_lit 1) v)))) L used

@[expose] noncomputable def assignX (w : Nat) (U : Nat → Nat) (L : List Nat) (t X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) X
    (fun q _ ih => Nat.lor (Nat.shiftLeft (pg w (mask w) (U q) t) (Nat.mul w q)) ih) L

@[expose] noncomputable def assignU (w : Nat) (U : Nat → Nat) (L : List Nat) (t used : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) used
    (fun q _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (pg w (mask w) (U q) t)) ih) L

@[expose] noncomputable def commAt (w : Nat) (G : Nat → Nat) (nG : Nat) (L : List Nat) (X : Nat) :
    Bool :=
  allL L fun q => allN nG fun j =>
    Nat.beq (pg w (mask w) X (pg w (mask w) (G j) q)) (pg w (mask w) (G j) (pg w (mask w) X q))

@[expose] noncomputable def centDfs (n w : Nat) (G : Nat → Nat) (nG nO : Nat) (O : Nat → List Nat)
    (U : Nat → Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ X _ => f X)
    (fun _ ih k X used => allN n fun t =>
      Bool.rec (motive := fun _ => Bool) true
        (letB (assignX w U (O k) t X) fun X' =>
          Bool.rec (motive := fun _ => Bool) true (ih (Nat.succ k) X' (assignU w U (O k) t used))
            (commAt w G nG (O k) X'))
        (assignOK w U (O k) t used))
    nO (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def presE (n w : Nat) (A : Nat → Nat) (x : Nat) : Bool :=
  allN n fun a => allN n fun b =>
    impB (bitB (A a) b) (bitB (A (pg w (mask w) x a)) (pg w (mask w) x b))

end CFSG.KC.Misc.Cent

end
