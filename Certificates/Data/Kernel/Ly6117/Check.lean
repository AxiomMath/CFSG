module

public import Certificates.Data.Kernel.LyS0.Check

public section

namespace CFSG.KD.Ly6117

open CFSG.KC.Enum CFSG.KD.LyS0

@[expose] noncomputable def letK (G GI : Nat → Nat) (l : Fin 6 × Bool) : Nat :=
  nIf(l.2, G l.1.val, GI l.1.val)

@[expose] noncomputable def wordK (G GI : Nat → Nat) (w : List (Fin 6 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) CFSG.KD.OrdLy.ONE
    (fun l _ ih => strictN ih (fun v => mul (letK G GI l) v)) w

@[expose] noncomputable def allK (G GI : Nat → Nat) (R : List (List (Fin 6 × Bool))) : Bool :=
  R.all (fun r => Nat.beq (wordK G GI r) CFSG.KD.OrdLy.ONE)

end CFSG.KD.Ly6117

end
