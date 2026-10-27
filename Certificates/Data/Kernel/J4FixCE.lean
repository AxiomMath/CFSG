module

public import Certificates.Data.Kernel.J4FixC

public section

namespace CFSG.KC.J4FixCE

open CFSG.KC.J4Q (mulJ vecJ getN)
open CFSG.KC.J4FixC (nth notK)
open CFSG.KC.Enum (strictN)

@[expose] noncomputable def prodK (c rm one : Nat) (G : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun n _ ih acc => strictN (mulJ c rm acc (getN one G n)) ih) w

@[expose] noncomputable def fixAllJ (rm M : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(Nat.blt p (Nat.pow (nat_lit 2) (nat_lit 112)),
      bAnd(Nat.beq (vecJ rm p M) p, ih))) L

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p t ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih' => bAnd(notK (Nat.beq p q), ih')) t, ih)) L

@[expose] noncomputable def eqB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notK y) y x

@[expose] noncomputable def treeAt (rm : Nat) (GM PT : List Nat) (PAR : List (Nat × Nat)) (i : Nat) :
    Bool :=
  bIf(Nat.beq i (nat_lit 0), true, bIf(Nat.beq i (nat_lit 77), true,
    Prod.rec (motive := fun _ => Bool) (fun p g => bAnd(Nat.blt p i, bAnd(Nat.blt g (nat_lit 2),
      bAnd(eqB (Nat.blt p (nat_lit 77)) (Nat.blt i (nat_lit 77)),
        Nat.beq (vecJ rm (nth (nat_lit 0) PT p) (nth (nat_lit 0) GM g)) (nth (nat_lit 0) PT i)))))
      (nth (nat_lit 0, nat_lit 0) PAR i)))

end CFSG.KC.J4FixCE

end
