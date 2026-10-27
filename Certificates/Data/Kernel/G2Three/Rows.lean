module

public import Certificates.Data.Kernel.G2Three.Defs

public section

namespace CFSG.KD.G2Three

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def q8K (I J : Nat) : Bool :=
  Nat.beq (MUL (MUL I I) (MUL I I)) ONE && !(Nat.beq (MUL I I) ONE) &&
    Nat.beq (MUL I I) (MUL J J) && Nat.beq (MUL (MUL I J) I) J

@[expose] noncomputable def threeK (Y I J : Nat) : Bool :=
  Nat.beq (MUL I Y) (MUL Y J) &&
    (Nat.beq (MUL J Y) (MUL Y (MUL I J)) || Nat.beq (MUL J Y) (MUL Y (MUL J I)))

@[expose] noncomputable def rowsK (XS XX W : Nat → Nat) : Bool :=
  allBelow 64 1 fun a => allBelow 64 1 fun b =>
    !(q8K (XS a) (XS b)) || (Nat.blt (W (Nat.add (Nat.mul 64 a) b)) 576 &&
      threeK (XX (W (Nat.add (Nat.mul 64 a) b))) (XS a) (XS b))

end CFSG.KD.G2Three

end
