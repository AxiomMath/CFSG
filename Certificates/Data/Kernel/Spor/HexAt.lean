module

public import Certificates.Data.Kernel.Misc.HexFlat

public section

namespace CFSG.KC.Misc.HexAt

open CFSG.KC.Enum CFSG.KC.Misc.HexFlat

@[expose] noncomputable def offF (G : Nat → Nat) (b : Nat) : Nat → Nat := fun j => G (Nat.add b j)

@[expose] noncomputable def hexAtK (cs : List Char) (off d n w N : Nat) (F : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun k => bIf(Nat.beq k (nat_lit 0), hexFlat [] d n w N F, false))
    (fun ch rest ih k => bIf(Nat.beq k (nat_lit 0), hexFlat (List.cons ch rest) d n w N F,
      bAnd(Nat.blt (Char.toNat ch) (nat_lit 128), strictB (Nat.sub k (nat_lit 1)) ih)))
    cs off

end CFSG.KC.Misc.HexAt

end
