module

public import Certificates.Data.Kernel.Co1M.Odd73

public section

namespace CFSG.KC.U45

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.SortTree CFSG.KC.Odd73

@[expose] noncomputable def opK (T p : Nat) : Nat := Nat.xor p (vmF (nat_lit 24) T p)

@[expose] noncomputable def witK (TA TB TC : Nat) (e : List Nat) (o : Nat) : Bool :=
  (fun v => andB (Nat.blt v (pw2 (nat_lit 24)))
    (andB (Nat.beq (opK TA (getL (nat_lit 0) e (Nat.add o (nat_lit 1)))) v)
    (andB (Nat.beq (opK TB (getL (nat_lit 0) e (Nat.add o (nat_lit 2)))) v)
      (Nat.beq (opK TC (getL (nat_lit 0) e (Nat.add o (nat_lit 3)))) v))))
  (getL (nat_lit 0) e o)

@[expose] noncomputable def lastO (nw : Nat) : Nat :=
  Nat.add (nat_lit 2) (Nat.mul (nat_lit 4) (Nat.sub nw (nat_lit 1)))

@[expose] noncomputable def wit2K (nw TA TB TC : Nat) (e : List Nat) : Bool :=
  andB (witK TA TB TC e (nat_lit 2)) (andB (witK TA TB TC e (lastO nw))
    (orB (Nat.blt nw (nat_lit 2))
      (notB (Nat.beq (getL (nat_lit 0) e (nat_lit 2)) (getL (nat_lit 0) e (lastO nw))))))

@[expose] noncomputable def gapK (rec : Nat → Nat) (n m g : Nat) : Bool :=
  andB (Nat.ble g n)
    (andB (orB (Nat.beq g (nat_lit 0)) (Nat.blt (valF (nat_lit 576) (rec (Nat.sub g (nat_lit 1)))) m))
      (orB (Nat.beq g n) (Nat.blt m (valF (nat_lit 576) (rec g)))))

@[expose] noncomputable def memK (i : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (Nat.beq a i) ih) L

@[expose] noncomputable def stRec (wl wp : Nat) (rec : Nat → Nat) (SI : List Nat) (i : Nat) : Bool :=
  (fun r => orB (andB (notB (Nat.beq (levF (nat_lit 576) wl r) (nat_lit 0)))
      (Nat.blt (letF (nat_lit 576) wl wp r) (nat_lit 8)))
    (memK i SI)) (rec i)

@[expose] noncomputable def stRun (wl wp : Nat) (rec : Nat → Nat) (SI : List Nat) (lo m : Nat) :
    Bool :=
  allN m fun j => stRec wl wp rec SI (Nat.add lo j)

@[expose] noncomputable def stE (nw R : Nat) (rec : Nat → Nat) (n : Nat) (e : List Nat) : Bool :=
  (fun X => (fun P => andB (Nat.blt (getL (nat_lit 0) e (nat_lit 0)) n)
      (orB (notB (Nat.beq P (mulF (nat_lit 24) X R)))
        (orB (gapK rec n P (getL (nat_lit 0) e (nat_lit 1)))
          (wit2K nw (trK (nat_lit 24) R) (trK (nat_lit 24) X) (trK (nat_lit 24) P) e))))
    (mulF (nat_lit 24) R X))
  (valF (nat_lit 576) (rec (getL (nat_lit 0) e (nat_lit 0))))

@[expose] noncomputable def c5E (nw R : Nat) (rec aux : Nat → Nat) (n : Nat) (e : List Nat) :
    Bool :=
  (fun i => (fun X => (fun P => (fun j => andB (Nat.blt i n)
      (andB (Nat.beq (clsA (aux i)) (nat_lit 5))
      (orB (Nat.beq X R)
      (orB (gapK rec n P j)
      (orB (andB (Nat.blt j n) (andB (Nat.beq (valF (nat_lit 576) (rec j)) P)
          (notB (Nat.beq (clsA (aux j)) (nat_lit 5)))))
        (wit2K nw (trK (nat_lit 24) R) (trK (nat_lit 24) X) (trK (nat_lit 24) P) e))))))
    (getL (nat_lit 0) e (nat_lit 1)))
    (mulF (nat_lit 24) R X))
    (valF (nat_lit 576) (rec i)))
  (getL (nat_lit 0) e (nat_lit 0))

@[expose] noncomputable def allE (L : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (f e) ih) L

@[expose] noncomputable def incE (L : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih x => andB (Nat.ble x (getL (nat_lit 0) e (nat_lit 0)))
      (ih (Nat.succ (getL (nat_lit 0) e (nat_lit 0))))) L

@[expose] noncomputable def lenE (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def headsE (L : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => List.cons (getL (nat_lit 0) e (nat_lit 0)) ih) L

@[expose] noncomputable def eqL (L M : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun a _ ih M => List.rec (motive := fun _ => Bool) false
      (fun b M' _ => andB (Nat.beq a b) (ih M')) M) L M

end CFSG.KC.U45

end
