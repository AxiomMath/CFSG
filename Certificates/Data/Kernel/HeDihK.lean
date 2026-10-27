module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.HeDih

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def evalWK {m : Nat} (n w : Nat) (G : Nat → Nat) (wd : List (Fin m × Bool)) :
    Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun x _ ih => pcomp n w (mask w)
      (Bool.rec (motive := fun _ => Nat) (pinvS n w (mask w) (G x.1.val)) (G x.1.val) x.2) ih) wd

@[expose] noncomputable def powK (n w r e : Nat) : Nat := ppow n w (mask w) (pidn n w) r e

@[expose] noncomputable def dihK (n w r s : Nat) : Bool :=
  (Nat.beq (powK n w r 4) (pidn n w) && !Nat.beq (powK n w r 2) (pidn n w) &&
    Nat.beq (pcomp n w (mask w) s s) (pidn n w) &&
    Nat.beq (pcomp n w (mask w) s (pcomp n w (mask w) r s)) (powK n w r 3)) &&
  (!Nat.beq s (powK n w r 0) && !Nat.beq s (powK n w r 1) && !Nat.beq s (powK n w r 2) &&
    !Nat.beq s (powK n w r 3))

@[expose] noncomputable def dihWK {m : Nat} (n w : Nat) (G : Nat → Nat) (wr ws : List (Fin m × Bool)) :
    Bool :=
  strictB (evalWK n w G wr) fun r => strictB (evalWK n w G ws) fun s => dihK n w r s

end CFSG.KC.HeDih

end
