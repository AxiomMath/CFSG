module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Misc.Clos

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def allR (lo cnt : Nat) (f : Nat → Bool) : Bool :=
  allN cnt fun d => f (Nat.add lo d)

@[expose] noncomputable def treeAt (M : Nat → Nat → Nat) (one : Nat) (G : Nat → Nat) (nG : Nat)
    (E PA : Nat → Nat) (k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (Nat.beq (E (nat_lit 0)) one)
    (fun _ _ => letB (PA k) fun r =>
      letB (Nat.land r (nat_lit 16777215)) fun p => letB (Nat.shiftRight r (nat_lit 24)) fun l =>
        andB (Nat.blt p k) (andB (Nat.blt l nG) (Nat.beq (E k) (M (E p) (G l))))) k

@[expose] noncomputable def sortAt (N : Nat) (E SG : Nat → Nat) (i : Nat) : Bool :=
  andB (Nat.blt (SG i) N)
    (impB (Nat.blt (Nat.succ i) N) (Nat.blt (E (SG i)) (E (SG (Nat.succ i)))))

@[expose] noncomputable def closedAt (M : Nat → Nat → Nat) (G : Nat → Nat) (nG N : Nat)
    (E CT : Nat → Nat) (k : Nat) : Bool :=
  allN nG fun j => letB (CT (Nat.add (Nat.mul k nG) j)) fun t =>
    andB (Nat.blt t N) (Nat.beq (E t) (M (E k) (G j)))

@[expose] noncomputable def letterK (n : Nat) (A : Nat → Nat) (nA l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (inv n (A (Nat.sub l nA))) (A l) (Nat.blt l nA)

@[expose] noncomputable def wordK (n : Nat) (A : Nat → Nat) (nA : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (one n) (fun l _ ih => mul n (letterK n A nA l) ih) w

@[expose] noncomputable def lettersK (nA : Nat) (w : List Nat) : Bool :=
  allL w fun l => Nat.blt l (Nat.add nA nA)

end CFSG.KC.Misc.Clos

end
