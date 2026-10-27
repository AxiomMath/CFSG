module

public import Certificates.Data.Kernel.Spor.MulH
public import Certificates.Data.Kernel.Spor.HKeyU

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def hsortPtKF (n w m cnt : Nat) (T HS HSI : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 HSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt,
      strictB (r32 HS (Nat.succ i)) (fun s' =>
        Nat.blt (hkeyU n w m (T s)) (hkeyU n w m (T s'))), true))))

end CFSG.KS.MulH

end
