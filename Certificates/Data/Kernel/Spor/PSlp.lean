module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.PSlp

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def nthD (l : List Nat) (i d : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun i' _ => ih i') i) l i

@[expose] noncomputable def letLP (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def stepP (n w d : Nat) (acc : List Nat) (a b : Nat) : Nat :=
  CFSG.KC.Loop.strictN (nthD acc a d) fun x =>
    CFSG.KC.Loop.strictN (nthD acc b d) fun y => pcomp n w (mask w) x y

@[expose] noncomputable def slpGo (n w fw d : Nat) : Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
    (fun _ ih P acc =>
      letLP (stepP n w d acc fld(P, nat_lit 0, mask fw) fld(P, fw, mask fw)) fun y =>
        letLP (Nat.shiftRight P (Nat.add fw fw)) fun P' => ih P' (List.cons y acc))

end CFSG.KC.PSlp

end
