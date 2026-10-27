module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.OrbLab

open CFSG.KC.Enum

@[expose] noncomputable def ptK (n m kG : Nat) (g : Nat → Nat → Nat) (L R P K D : Nat → Nat) (x : Nat) : Bool :=
  Nat.blt (L x) m && Nat.ble (R (L x)) x &&
    allN kG (fun k => !(Nat.blt (g k x) n) || Nat.beq (L (g k x)) (L x)) &&
    (Nat.beq x (R (L x)) || (Nat.blt (P x) n && Nat.blt (K x) kG && Nat.beq (g (K x) (P x)) x &&
      Nat.blt (D (P x)) (D x)))

@[expose] noncomputable def rootK (n m : Nat) (L R : Nat → Nat) (c : Nat) : Bool :=
  Nat.blt (R c) n && Nat.beq (L (R c)) c && (!(Nat.blt (c + 1) m) || Nat.blt (R c) (R (c + 1)))

@[expose] noncomputable def orbRecK (n m kG : Nat) (g : Nat → Nat → Nat) (L R P K D : Nat → Nat) : Bool :=
  Nat.ble m n && allN n (ptK n m kG g L R P K D) && allN m (rootK n m L R)

end CFSG.KS.OrbLab

end
