module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.McLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def yPredK (Y YI : Nat → Nat) (z j : Nat) : Bool :=
  bIf(Nat.beq z (Y j), true, Nat.beq z (YI j))

@[expose] noncomputable def firstK (Y YI : Nat → Nat) (z v : Nat) : Bool :=
  bAnd(Nat.blt v (nat_lit 10), bAnd(yPredK Y YI z v,
    allN v (fun j => bIf(yPredK Y YI z j, false, true))))

@[expose] noncomputable def anyYK (Y YI : Nat → Nat) (z : Nat) : Bool :=
  bIf(allN (nat_lit 10) (fun j => bIf(yPredK Y YI z j, false, true)), false, true)

@[expose] noncomputable def brK (cnt : Nat) (T SRT : Nat → Nat) (x s : Nat) : Bool :=
  bAnd(Nat.ble s cnt,
    bAnd(bIf(Nat.beq s (nat_lit 0), true, Nat.blt (T (r32 SRT (Nat.sub s (nat_lit 1)))) x),
      bIf(Nat.beq s cnt, true, Nat.blt x (T (r32 SRT s)))))

end CFSG.KS.McLAS

end
