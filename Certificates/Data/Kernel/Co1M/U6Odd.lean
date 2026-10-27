module

public import Certificates.Data.Kernel.Co1M.InvFam

public section

namespace CFSG.KC.U6Odd

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def actR (U : List Nat) (l X : Nat) : Nat :=
  mulW (nat_lit 24) X (getL (nat_lit 0) U l)

@[expose] noncomputable def actH (H Hi : List Nat) (l X : Nat) : Nat :=
  mulW (nat_lit 24) (mulW (nat_lit 24) (getL (nat_lit 0) H l) X) (getL (nat_lit 0) Hi l)

@[expose] noncomputable def xcK (c : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih m => Nat.xor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) x
      (Nat.beq (Nat.mod m (nat_lit 2)) (nat_lit 1))) (ih (Nat.div m (nat_lit 2)))) c

@[expose] noncomputable def newOK (L : Nat → Nat) (b : List Nat) (k : Nat) (c : List Nat) : Bool :=
  allN (pw2 k) fun j => Nat.beq (L (xcK c (Nat.add (pw2 k) j))) (L (xcK b (Nat.add (pw2 k) j)))

@[expose] noncomputable def tupStep (L : Nat → Nat) (W b : List Nat) (k : Nat)
    (ps : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun c _ ih => List.rec (motive := fun _ => List (List Nat)) ih
      (fun x _ ih2 => (fun c' => Bool.rec (motive := fun _ => List (List Nat)) ih2
        (List.cons c' ih2) (newOK L b k c')) (List.append c (List.cons x List.nil))) W) ps

@[expose] noncomputable def tupIter (L : Nat → Nat) (W b : List Nat) (n : Nat) :
    Nat → List (List Nat) → List (List Nat) :=
  Nat.rec (motive := fun _ => Nat → List (List Nat) → List (List Nat)) (fun _ ps => ps)
    (fun _ ih k ps => ih (Nat.succ k) (tupStep L W b k ps)) n

@[expose] noncomputable def tupsK (L : Nat → Nat) (W b : List Nat) (u₁ u₂ : Nat) : List (List Nat) :=
  tupIter L W b (Nat.sub (lenL b) (nat_lit 2)) (nat_lit 2) (List.cons (List.cons u₁ (List.cons u₂ List.nil)) List.nil)

@[expose] noncomputable def lenLL (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def tupK (L : Nat → Nat) (W : List Nat) (u₁ u₂ : Nat) (b : List Nat) (t : Nat) :
    Bool :=
  Nat.ble (lenLL (tupsK L W b u₁ u₂)) t

@[expose] noncomputable def normK (X G p : Nat) : Bool :=
  anyN (Nat.sub p (nat_lit 1)) fun j =>
    Nat.beq (mulF (nat_lit 24) X G) (mulF (nat_lit 24) (powK (nat_lit 24) G (Nat.succ j)) X)

@[expose] noncomputable def witK (val : Nat → Nat) (n i w : Nat) : Bool :=
  orB (Nat.beq w (nat_lit 0))
    (andB (allN (nat_lit 3) fun t => (fun j k => andB (Nat.blt j n) (andB (Nat.blt k n)
        (Nat.beq (mulW (nat_lit 24) (val j) (val i)) (mulW (nat_lit 24) (val k) (val j)))))
        (fget w (Nat.mul (nat_lit 2) t) (nat_lit 10)) (fget w (Nat.succ (Nat.mul (nat_lit 2) t)) (nat_lit 10)))
      ((fun k0 k1 k2 => andB (notB (Nat.beq k0 k1)) (andB (notB (Nat.beq k0 k2))
        (andB (notB (Nat.beq k1 k2)) (andB (notB (Nat.beq k0 i)) (andB (notB (Nat.beq k1 i))
          (notB (Nat.beq k2 i)))))))
        (fget w (nat_lit 1) (nat_lit 10)) (fget w (nat_lit 3) (nat_lit 10)) (fget w (nat_lit 5) (nat_lit 10))))

@[expose] noncomputable def zerosK (n : Nat) (f : Nat → Nat) : Nat :=
  sumN n fun i => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (f i) (nat_lit 0))

end CFSG.KC.U6Odd

end
