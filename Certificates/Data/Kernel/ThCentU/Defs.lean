module

public import Certificates.Data.Kernel.ThCent.Pin
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.ThCentU

open CFSG.KC.Th CFSG.KC.ThCent

@[expose] noncomputable def dig3 (a p : Nat) : Nat :=
  Nat.mod (Nat.div a (Nat.pow (nat_lit 3) p)) (nat_lit 3)

@[expose] noncomputable def dot5 (a b i j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.mul (dig3 a (Nat.add (Nat.mul (nat_lit 5) i) k))
      (dig3 b (Nat.add (Nat.mul (nat_lit 5) k) j)))) (nat_lit 5)

@[expose] noncomputable def prod5 (z a b : Nat) : Bool :=
  CFSG.KC.Ord.andB (Nat.blt z (nat_lit 847288609443))
    (CFSG.KC.LQT.P.allN (nat_lit 25) fun q =>
      Nat.beq (dig3 z q) (Nat.mod (dot5 a b (Nat.div q (nat_lit 5)) (Nat.mod q (nat_lit 5)))
        (nat_lit 3)))

@[expose] noncomputable def one5 (z : Nat) : Bool :=
  CFSG.KC.Ord.andB (Nat.blt z (nat_lit 847288609443))
    (CFSG.KC.LQT.P.allN (nat_lit 25) fun q =>
      Nat.beq (dig3 z q) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
        (Nat.beq (Nat.div q (nat_lit 5)) (Nat.mod q (nat_lit 5)))))

@[expose] noncomputable def node5 (G : Nat → Nat) (nG : Nat) (E PA : Nat → Nat) (k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (one5 (E (nat_lit 0)))
    (fun _ _ => CFSG.KC.LQT.P.letB (PA k) fun r =>
      CFSG.KC.LQT.P.letB (Nat.land r (nat_lit 16777215)) fun p =>
        CFSG.KC.LQT.P.letB (Nat.shiftRight r (nat_lit 24)) fun l =>
          CFSG.KC.Ord.andB (Nat.blt p k) (CFSG.KC.Ord.andB (Nat.blt l nG)
            (prod5 (E k) (E p) (G l)))) k

@[expose] noncomputable def wordFromH (c rm H₁ H₂ : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictF (mulB c rm acc
      (Bool.rec (motive := fun _ => Nat) H₂ H₁ (Nat.beq l (nat_lit 0)))) ih) w

@[expose] noncomputable def wordH (c rm ONE H₁ H₂ : Nat) (w : List Nat) : Nat :=
  wordFromH c rm H₁ H₂ w ONE

@[expose] noncomputable def rpw (M : Nat → Nat) (ONE i e : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (M (Nat.add (nat_lit 5) i)) (M i) (Nat.beq e (nat_lit 1)))
    ONE (Nat.beq e (nat_lit 0))

@[expose] noncomputable def phiK (c rm ONE : Nat) (M : Nat → Nat) (A j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => strictF (mulB c rm acc
      (rpw M ONE i (dig3 A (Nat.add (Nat.mul (nat_lit 5) j) i)))) fun v => v) (nat_lit 5)

@[expose] noncomputable def conjK (c rm ONE : Nat) (M : Nat → Nat) (A l j : Nat) : Bool :=
  Nat.beq (mulB c rm (M (Nat.add (nat_lit 10) l)) (M j))
    (mulB c rm (phiK c rm ONE M A j) (M (Nat.add (nat_lit 10) l)))

@[expose] noncomputable def keyK (rm : Nat) (M : Nat → Nat) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (M (nat_lit 12))
    (fun i acc => strictF (dig3 c i) fun e => Bool.rec (motive := fun _ => Nat)
      (strictF (vecB rm acc (Bool.rec (motive := fun _ => Nat) (M (Nat.add (nat_lit 5) i)) (M i)
        (Nat.beq e (nat_lit 1)))) fun v => v) acc (Nat.beq e (nat_lit 0))) (nat_lit 5)

end CFSG.KC.ThCentU

end
