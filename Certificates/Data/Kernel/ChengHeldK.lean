module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.ChengHeld

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] noncomputable def wfK (n w : Nat) (G GI : Nat → Nat) (acc : Nat)
    (wd : List (Fin 7 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun l _ ih a => ih (pcomp n w (mask w) a
      (Bool.rec (motive := fun _ => Nat) (GI l.1.val) (G l.1.val) l.2))) wd acc

@[expose] noncomputable def relK (n w : Nat) (G GI : Nat → Nat) (ws : List (List (Fin 7 × Bool))) :
    Bool :=
  ws.all fun wd => Nat.beq (wfK n w G GI (pidn n w) wd) (pidn n w)

@[expose] noncomputable def invK (n w : Nat) (G GI : Nat → Nat) (k : Nat) : Bool :=
  allN k fun j => bAnd(canonK n w (mask w) (Nat.mul n w) (GI j),
    Nat.beq (pcomp n w (mask w) (G j) (GI j)) (pidn n w))

end CFSG.KC.ChengHeld

end
