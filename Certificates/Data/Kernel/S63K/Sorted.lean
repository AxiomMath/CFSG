module

public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.S63K

@[expose] noncomputable def bsK (P S : Nat → Nat) (y : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => bif Nat.ble (hi - lo) 1 then lo
      else bif Nat.ble (P (S ((lo + hi) / 2))) y then ih ((lo + hi) / 2) hi
      else ih lo ((lo + hi) / 2))

@[expose] noncomputable def memAt (P S : Nat → Nat) (N y k : Nat) : Nat :=
  bif Nat.blt k N && Nat.ble (P (S k)) y && (Nat.beq (k + 1) N || Nat.blt y (P (S (k + 1)))) then
    (bif Nat.beq (P (S k)) y then 1 else 0) else 2

@[expose] noncomputable def memS (P S : Nat → Nat) (N y : Nat) : Nat :=
  bif Nat.blt y (P (S 0)) then 0 else memAt P S N y (bsK P S y 32 0 N)

end CFSG.KC.S63K

end
