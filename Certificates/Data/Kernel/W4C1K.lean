module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.W4C1

open CFSG.KD.Sp62 CFSG.KC.Loop

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def all5 (G : Nat → Nat) (F : Nat → Bool) : Bool :=
  F (G 0) && (F (G 1) && (F (G 2) && (F (G 3) && (F (G 4) && true))))

@[expose] noncomputable def cInvF (G : Nat → Nat) (Z : Nat) : Bool :=
  Nat.beq (MULF Z Z) ONE && !Nat.beq Z ONE && all5 G fun S => Nat.beq (MULF S Z) (MULF Z S)

@[expose] noncomputable def condXF (G : Nat → Nat) (Z X : Nat) : Bool :=
  Nat.beq (MULF X X) ONE && !Nat.beq X ONE && !Nat.beq X Z && Nat.beq (MULF X Z) (MULF Z X) &&
    all5 G fun S => Nat.beq (MULF S X) (MULF X S) || Nat.beq (MULF S X) (MULF (MULF X Z) S)

@[expose] noncomputable def condYF (G : Nat → Nat) (Z X Y : Nat) : Bool :=
  Nat.beq (MULF Y Y) ONE && !Nat.beq Y ONE && !Nat.beq Y Z && !Nat.beq Y X &&
    !Nat.beq Y (MULF X Z) && Nat.beq (MULF Y Z) (MULF Z Y) && Nat.beq (MULF Y X) (MULF X Y) &&
    all5 G fun S => Nat.beq (MULF S Y) (MULF Y S) || Nat.beq (MULF S Y) (MULF (MULF Y Z) S) ||
      Nat.beq (MULF S Y) (MULF (MULF Y X) S) || Nat.beq (MULF S Y) (MULF (MULF Y (MULF X Z)) S)

@[expose] noncomputable def inT8F (Z X Y W : Nat) : Bool :=
  Nat.beq W ONE || Nat.beq W Z || Nat.beq W X || Nat.beq W (MULF X Z) || Nat.beq W Y ||
    Nat.beq W (MULF Y Z) || Nat.beq W (MULF Y X) || Nat.beq W (MULF Y (MULF X Z))

@[expose] noncomputable def chainX (R : Nat → Nat) (o : Nat) (G : Nat → Nat) (W hi Z X : Nat) :
    Bool :=
  !condXF G Z X || allBelow 512 hi fun c =>
    letB (recX R o c) fun Y => !condYF G Z X Y || inT8F Z X Y W

@[expose] noncomputable def chainZ (R : Nat → Nat) (o : Nat) (G : Nat → Nat) (W hi Z : Nat) :
    Bool :=
  !cInvF G Z || allBelow 512 hi fun b => letB (recX R o b) fun X => chainX R o G W hi Z X

@[expose] noncomputable def chainK (R : Nat → Nat) (o : Nat) (G : Nat → Nat) (W hi : Nat) : Bool :=
  allBelow 512 hi fun a => letB (recX R o a) fun Z => chainZ R o G W hi Z

end CFSG.KD.W4C1

end
