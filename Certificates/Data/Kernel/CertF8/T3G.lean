module

public import Certificates.Data.Kernel.G28.T3

public section

namespace CFSG.KC.CertF8.T3G

open CFSG.KC.G28

@[expose] def ph1 (p q r v : Nat) (e : Nat × Nat) : Nat × Nat :=
  ((p * e.1 + r * e.2) % 9, (q * e.1 + v * e.2) % 9)

@[expose] def phG (p q r v c : Nat) (e : Nat × Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) e (fun _ acc => ph1 p q r v acc) c

@[expose] def pcMulG (p q r v x y : Nat) : Nat :=
  pcIdx (x / 27 + (phG p q r v (x % 3) (y / 27, y / 3 % 9)).1)
    (x / 3 % 9 + (phG p q r v (x % 3) (y / 27, y / 3 % 9)).2) (x % 3 + y % 3)

@[expose] def pwG (p q r v x n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => pcMulG p q r v acc x) n

@[expose] def pcInvG (p q r v x : Nat) : Nat :=
  pcMulG p q r v (pcIdx 0 0 (3 - x % 3)) (pcIdx (9 - x / 27 % 9) (9 - x / 3 % 9) 0)

@[expose] def pcInvOKG (p q r v : Nat) : Bool :=
  (List.range 243).all fun x => Nat.beq (pcMulG p q r v x (pcInvG p q r v x)) 0

@[expose] noncomputable def relG (p q r v U Z O : Nat) : Bool :=
  Nat.beq (powP U 9) idP && Nat.beq (powP Z 9) idP && Nat.beq (powP O 3) idP &&
  Nat.beq (mulP U Z) (mulP Z U) &&
  Nat.beq (mulP O U) (mulP (mulP (powP U p) (powP Z q)) O) &&
  Nat.beq (mulP O Z) (mulP (mulP (powP U r) (powP Z v)) O)

end CFSG.KC.CertF8.T3G

end
