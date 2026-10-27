module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.Item434Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def twoK (a b j : Nat) : Nat := [a, b].getD j 0

noncomputable abbrev pcK (n w p q : Nat) : Nat := pcomp n w (mask w) p q

noncomputable abbrev pwK (n w p k : Nat) : Nat := ppow n w (mask w) (pidn n w) p k

@[expose] noncomputable def pNK (n w e₁ e₂ : Nat) (ab : Nat × Nat) : Nat :=
  pcK n w (pwK n w e₁ ab.1) (pwK n w e₂ ab.2)

@[expose] noncomputable def e9K (n w e₁ e₂ : Nat) : Bool :=
  Nat.beq (pwK n w e₁ 3) (pidn n w) && Nat.beq (pwK n w e₂ 3) (pidn n w) &&
    Nat.beq (pcK n w e₁ e₂) (pcK n w e₂ e₁) &&
    !Nat.beq e₁ (pidn n w) && !Nat.beq e₂ (pidn n w) && !Nat.beq e₂ e₁ &&
    !Nat.beq e₂ (pwK n w e₁ 2)

@[expose] noncomputable def sigK (n w : Nat) (S : Nat → Nat) (k : Nat) (ords : List Nat)
    (ps : List (Nat × Nat)) (e₁ e₂ : Nat) : Bool :=
  allN k fun i =>
    Nat.beq (pwK n w (S i) (ords.getD i 0)) (pidn n w) && !(ords.getD i 0 % 3 == 0) &&
      Nat.beq (pcK n w (S i) (pNK n w e₁ e₂ (ps.getD i (0, 0))))
        (pcK n w (pNK n w e₁ e₂ (ps.getD i (0, 0))) (S i)) &&
      !Nat.beq (pNK n w e₁ e₂ (ps.getD i (0, 0))) (pidn n w)

@[expose] noncomputable def cmK (n w x xi y yi : Nat) : Nat :=
  pcK n w (pcK n w x y) (pcK n w xi yi)

@[expose] noncomputable def heisK (n w x y z : Nat) : Bool :=
  Nat.beq (pwK n w x 3) (pidn n w) && Nat.beq (pwK n w y 3) (pidn n w) &&
    Nat.beq (pcK n w z x) (pcK n w x z) && Nat.beq (pcK n w z y) (pcK n w y z) &&
    !Nat.beq z (pidn n w)

end CFSG.KC.Item434Gen

end
