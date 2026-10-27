module

public import Certificates.Data.Kernel.Spor.HKeyB

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def hsortPtB (n w m cnt : Nat) (T HS HSI : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 HSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt,
      Nat.blt (hkeyB n w m (T s)) (hkeyB n w m (T (r32 HS (Nat.succ i)))), true))))

end CFSG.KS.MulH

end
