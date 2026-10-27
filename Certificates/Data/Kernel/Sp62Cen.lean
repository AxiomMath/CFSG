module

public import Certificates.Data.Kernel.Sp62Twin

public section

namespace CFSG.KD.Sp62

open CFSG.KC.Loop

@[expose] noncomputable def inA0 (Z0 Z1 Z2 y : Nat) : Bool :=
  (List.range 3).any fun a => (List.range 3).any fun b => (List.range 3).any fun c =>
    Nat.beq y (VC Z0 Z1 Z2 a b c)

@[expose] noncomputable def cenF (Z0 Z1 Z2 y : Nat) : Bool :=
  !(Nat.beq (MULF y Z1) (MULF Z1 y) && Nat.beq (MULF y Z2) (MULF Z2 y)) || inA0 Z0 Z1 Z2 y

@[expose] noncomputable def cenK (Z0 Z1 Z2 : Nat) (X : Nat → Nat) (n hi : Nat) : Bool :=
  allBelow n hi fun t => cenF Z0 Z1 Z2 (X t)

end CFSG.KD.Sp62

end
