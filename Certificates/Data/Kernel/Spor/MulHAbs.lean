module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def absK (n w m cnt : Nat) (T HS : Nat → Nat) (q p : Nat) : Bool :=
  strictB (hkeyK n w m q) (fun h => bAnd(Nat.ble p cnt,
    bAnd(bIf(Nat.beq p 0, true, Nat.blt (hkeyK n w m (T (r32 HS (Nat.sub p 1)))) h),
      bIf(Nat.blt p cnt, Nat.blt h (hkeyK n w m (T (r32 HS p))), true))))

@[expose] noncomputable def memK (n w m cnt : Nat) (T HS : Nat → Nat) (q pos br : Nat) : Bool :=
  bIf(Nat.blt pos cnt, Nat.beq (T pos) q, absK n w m cnt T HS q br)

end CFSG.KS.MulH

end
