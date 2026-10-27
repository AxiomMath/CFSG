module

public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KC.TabWord

open CFSG.KC.Enum CFSG.KS

@[expose] def fdN (w x i : Nat) : Nat := x / 2 ^ (w * i) % 2 ^ w

@[expose] noncomputable def wordK (n w idn : Nat) (L : Int → Nat) (u : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun z _ ih => strictN ih fun T => pcomp n w (mask w) (L z) T) u

@[expose] noncomputable def findK (w P y : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => Bool.rec (findK w P y k) k (Nat.beq (fdN w P k) y)

@[expose] noncomputable def pinvK (n w P : Nat) : Nat := pmk n w fun y => findK w P y n

@[expose] def allLtK (n w P : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => allLtK n w P k && Nat.blt (fdN w P k) n

end CFSG.KC.TabWord

end
