module

public import Certificates.Data.Kernel.CoreD2K.Check

public section

namespace CFSG.KS.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2

@[expose] noncomputable def exRel (n w Z X Y t : Nat) : Bool :=
  bAnd(Nat.beq (pw n w Z 5) (pidn n w), bAnd(Nat.beq (pw n w X 5) (pidn n w),
  bAnd(Nat.beq (pw n w Y 5) (pidn n w),
  bAnd(Nat.beq (pcomp n w (mask w) Z X) (pcomp n w (mask w) X Z),
  bAnd(Nat.beq (pcomp n w (mask w) Z Y) (pcomp n w (mask w) Y Z),
    Nat.beq (pcomp n w (mask w) Y X)
      (pcomp n w (mask w) (pcomp n w (mask w) X Y) (pw n w Z t)))))))

@[expose] noncomputable def exGen (n w Z X Y G a b c : Nat) : Bool :=
  Nat.beq G (pcomp n w (mask w) (pcomp n w (mask w) (pw n w Z a) (pw n w X b)) (pw n w Y c))

@[expose] noncomputable def pit (w P : Nat) (a i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ r => pg w (mask w) P r) a

@[expose] noncomputable def nfPts (w Z X Y p : Nat) : List Nat :=
  (List.range 125).map fun k => pit w Z (k / 25) (pit w X (k / 5 % 5) (pit w Y (k % 5) p))

end CFSG.KS.CoreD2K

end
