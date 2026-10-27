module

public import Certificates.Data.Kernel.PGrp

public section

namespace CFSG.KC.E81IK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def covIW (nd : Nat) (ND : Nat → Nat) (DT : Nat → Nat → Nat)
    (Z : Nat) (ZW : Nat → Nat) (s t j : Nat) : Bool :=
  Nat.blt t nd && Nat.blt j (ND t) && Nat.blt 0 (ZW t) && Nat.ble (ZW t) (ND t) &&
    Nat.beq s (DT t j) && Nat.beq Z (DT t (ZW t - 1))

@[expose] noncomputable def covIK (n w nd : Nat) (ND : Nat → Nat) (DT : Nat → Nat → Nat)
    (Z Z2 : Nat) (ZW : Nat → Nat) (c s : Nat) : Bool :=
  (Nat.beq c 0 && (Nat.beq s Z || Nat.beq s Z2 || Nat.beq s (pidn n w))) ||
    (Nat.blt 0 c && Nat.ble c n &&
      !Nat.beq (pg w (mask w) s (pg w (mask w) s (pg w (mask w) s (c - 1)))) (c - 1)) ||
    (Nat.blt n c && covIW nd ND DT Z ZW s ((c - 1 - n) % nd) ((c - 1 - n) / nd))

end CFSG.KC.E81IK

end
