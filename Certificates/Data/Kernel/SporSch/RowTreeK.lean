module

public import Certificates.Data.Kernel.SporSch.RuTreeK

public section

namespace CFSG.KS.RowTree

open CFSG.KLC.Fi22 CFSG.KS.RuTree

@[expose] noncomputable def edgeK (NW0 NW1 n rx rp c : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight rx n) (nat_lit 0))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (Nat.beq (applyNW NW1 (nat_lit 1) rx) rp)
          (Nat.beq (applyNW NW0 (nat_lit 1) rx) rp) (Nat.beq c (nat_lit 3)))
        (Nat.beq (applyNW NW1 (nat_lit 1) rp) rx) (Nat.beq c (nat_lit 2)))
      (Nat.beq (applyNW NW0 (nat_lit 1) rp) rx) (Nat.beq c (nat_lit 1)))

@[expose] noncomputable def reachK (par : Nat → Nat) (f x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun y => Nat.beq y (nat_lit 0))
    (fun _ ih y => Bool.rec (motive := fun _ => Bool) (sB (par y) ih) true (Nat.beq y (nat_lit 0)))
    f x

@[expose] noncomputable def rowK (NW0 NW1 n : Nat) (Row par lab : Nat → Nat) (f x : Nat) : Bool :=
  andB (reachK par f x)
    (sB (Row x) (fun rx => sB (Row (par x)) (fun rp => edgeK NW0 NW1 n rx rp (lab x))))

@[expose] noncomputable def rootK (n r : Nat) (lab : Nat → Nat) (c : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight r n) (nat_lit 0))
    (rngK (nat_lit 0) n (fun y => (fun e => Bool.rec (motive := fun _ => Bool) (notB e) e (bt r y))
      (Nat.beq (lab y) c)))

@[expose] noncomputable def fpK (Row w : Nat → Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add (Nat.mul (nat_lit 2) acc)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (bt (Row (w i)) x))) k

@[expose] noncomputable def keyK (F Lk : Nat → Nat) (m i : Nat) : Bool :=
  orB (notB (Nat.blt (Nat.succ i) m)) (Nat.blt (F (Lk i)) (F (Lk (Nat.succ i))))

@[expose] noncomputable def coverK (inS : Nat → Bool) (Pk Lk : Nat → Nat) (m x : Nat) : Bool :=
  orB (notB (inS x)) (andB (Nat.blt (Pk x) m) (Nat.beq (Lk (Pk x)) x))

end CFSG.KS.RowTree

end
