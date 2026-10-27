module

public import Init

public section

namespace CFSG.KC.FischerB

inductive BT where
  | lf (v : Nat)
  | nd (l r : BT)

@[expose] noncomputable def getB (T : BT) : Nat → Nat :=
  BT.rec (motive := fun _ => Nat → Nat) (fun v _ => v)
    (fun _ _ ihl ihr i => Bool.rec (motive := fun _ => Nat) (ihl (Nat.shiftRight i 1))
      (ihr (Nat.shiftRight i 1)) (Nat.beq (Nat.land i 1) 1)) T

@[expose] noncomputable def setB (T : BT) : Nat → Nat → BT :=
  BT.rec (motive := fun _ => Nat → Nat → BT) (fun _ _ v => BT.lf v)
    (fun l r ihl ihr i v => Bool.rec (motive := fun _ => BT)
      (BT.nd (ihl (Nat.shiftRight i 1) v) r) (BT.nd l (ihr (Nat.shiftRight i 1) v))
      (Nat.beq (Nat.land i 1) 1)) T

@[expose] noncomputable def mkB (c : Nat) (d : Nat) : BT :=
  Nat.rec (motive := fun _ => BT) (BT.lf c) (fun _ ih => BT.nd ih ih) d

@[expose] noncomputable def getT (T : BT) (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (getB T i) (Nat.blt i 2048)

@[expose] noncomputable def setT (T : BT) (i v : Nat) : BT :=
  Bool.rec (motive := fun _ => BT) T (setB T i v) (Nat.blt i 2048)

end CFSG.KC.FischerB

end
