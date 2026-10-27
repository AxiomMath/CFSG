module

public import Certificates.Data.Kernel.FiveLocK
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.GFR3K

open CFSG.KC.Enum CFSG.KS CFSG.KC.B3S3K CFSG.KC.FiveLocK

@[expose] noncomputable def gfr3CntK (n w N : Nat) (T : Nat → Nat) (x : Nat) : Nat :=
  CFSG.KLie.CT.sumN N fun j => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (commK n w (T j) x)

@[expose] noncomputable def gfr3AtK (n w N : Nat) (T : Nat → Nat) (Nc e f i : Nat) : Bool :=
  (!(Nat.beq (pw n w (T i) 2) (pidn n w)) || Nat.beq (T i) (pidn n w) ||
      decide (gfr3CntK n w N T (T i) * 2 ^ e < Nc)) &&
    (!(Nat.beq (pw n w (T i) 5) (pidn n w)) || Nat.beq (T i) (pidn n w) ||
      decide (gfr3CntK n w N T (T i) * (2 ^ e * 5 ^ f) < Nc))

end CFSG.KC.GFR3K

end
