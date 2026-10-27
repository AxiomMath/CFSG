module

public import Certificates.Data.Kernel.PGrp

public section

namespace CFSG.KC.E81K

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def zwK (n w nh : Nat) (H ND : Nat → Nat) (DT : Nat → Nat → Nat)
    (Z : Nat) (ZW : Nat → Nat) (x : Nat) : Bool :=
  Nat.beq (ZW x) 0 || (Nat.ble (ZW x) (ND (x / nh)) &&
    Nat.beq (pcomp n w (mask w) (H (x % nh)) Z)
      (pcomp n w (mask w) (DT (x / nh) (ZW x - 1)) (H (x % nh))))

@[expose] noncomputable def covW (n w nh nd : Nat) (H ND : Nat → Nat) (DT : Nat → Nat → Nat)
    (ZW : Nat → Nat) (s x j : Nat) : Bool :=
  Nat.blt x (nh * nd) && Nat.blt j (ND (x / nh)) && Nat.blt 0 (ZW x) &&
    Nat.beq (pcomp n w (mask w) (H (x % nh)) s)
      (pcomp n w (mask w) (DT (x / nh) j) (H (x % nh)))

@[expose] noncomputable def covK (n w nh nd : Nat) (H ND : Nat → Nat) (DT : Nat → Nat → Nat)
    (Z Z2 : Nat) (ZW : Nat → Nat) (c s : Nat) : Bool :=
  (Nat.beq c 0 && (!Nat.beq (pcomp n w (mask w) s (pcomp n w (mask w) s s)) (pidn n w) ||
      Nat.beq s (pidn n w) || Nat.beq s Z || Nat.beq s Z2)) ||
    (Nat.blt 0 c && covW n w nh nd H ND DT ZW s ((c - 1) % (nh * nd)) ((c - 1) / (nh * nd)))

end CFSG.KC.E81K

end
