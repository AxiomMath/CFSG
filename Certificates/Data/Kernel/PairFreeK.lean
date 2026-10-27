module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.PairFree

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def cmK (n w p q : Nat) : Nat := pcomp n w (mask w) p q

@[expose] noncomputable def invK (n w p : Nat) : Bool :=
  Nat.beq (cmK n w p p) (pidn n w) && !Nat.beq p (pidn n w)

@[expose] noncomputable def fiveK (n w p : Nat) : Bool :=
  Nat.beq (cmK n w p (cmK n w p (cmK n w p (cmK n w p p)))) (pidn n w) && !Nat.beq p (pidn n w)

@[expose] noncomputable def lineK (n w X p : Nat) : Bool :=
  Nat.beq p (pidn n w) || Nat.beq p X || Nat.beq p (cmK n w X X) ||
    Nat.beq p (cmK n w X (cmK n w X X)) || Nat.beq p (cmK n w X (cmK n w X (cmK n w X X)))

@[expose] noncomputable def pairFreeK (n w N : Nat) (T : Nat → Nat) (X : Nat) (I F : List Nat) :
    Bool :=
  allN N (fun j => !(fiveK n w (T j) && !lineK n w X (T j)) || F.contains j) &&
    allN N (fun i => !invK n w (T i) || I.contains i) &&
    I.all fun i => F.all fun j => !Nat.beq (cmK n w (T i) (T j)) (cmK n w (T j) (T i))

end CFSG.KC.PairFree

end
