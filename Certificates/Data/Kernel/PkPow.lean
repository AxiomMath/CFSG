module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.PkPow

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ppw (n w p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w)
    (fun _ ih => strictN ih (fun q => pcomp n w (mask w) p q)) e

@[expose] noncomputable def wv {m : Nat} (n w : Nat) (gs gis : Nat → Nat)
    (W : List (Fin m × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun x _ ih => strictN ih (fun q => pcomp n w (mask w)
      (Bool.rec (motive := fun _ => Nat) (gis x.1.val) (gs x.1.val) x.2) q)) W

@[expose] noncomputable def nfix (n w p : Nat) : Nat :=
  foldN n (fun x c => nIf(Nat.beq (pg w (mask w) p x) x, Nat.succ c, c)) (nat_lit 0)

end CFSG.KC.PkPow

end
