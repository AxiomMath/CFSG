module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.ClosW

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.Clos

@[expose] noncomputable def wLetter (n w : Nat) (A : Nat → Nat) (nA l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pinvS n w (mask w) (A (Nat.sub l nA))) (A l) (Nat.blt l nA)

@[expose] noncomputable def wWord (n w : Nat) (A : Nat → Nat) (nA : Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun l _ ih => pcomp n w (mask w) (wLetter n w A nA l) ih) wd

@[expose] noncomputable def wWordAt (n w : Nat) (A : Nat → Nat) (nA : Nat) (W : Nat → List Nat)
    (C : Nat → Nat) (j : Nat) : Bool :=
  andB (lettersK nA (W j)) (Nat.beq (wWord n w A nA (W j)) (C j))

end CFSG.KC.Misc.ClosW

end
