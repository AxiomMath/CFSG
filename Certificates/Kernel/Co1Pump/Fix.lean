module

public import Certificates.Data.Kernel.Co1PumpFix
public import Certificates.Kernel.Co1Pump.FixData
public import Certificates.Kernel.Co1Pairs.Data
public import Certificates.Kernel.Co1FiveK.Chk
public import Certificates.Kernel.VecCert.Co1.A
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
public import Certificates.Data.Kernel.F2Set24
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.Co1Pairs CFSG.KD.Co1PumpFix CFSG.KC.Co1M CFSG.KC.VecK

@[expose] noncomputable def ch36909X (x : Nat) : Bool :=
  orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x

theorem ch36909w : bAnd(entsK CFSG.KD.Co1Pairs.R2 JW FW 0, bAnd(Nat.beq (popK JW) 6,
    Nat.beq (cntK ch36909X JW FW 0 0 0) 27)) = true := by quickRfl

@[expose] noncomputable def ch36909a1 (M J : Nat) (F : List (Nat × Nat × Nat)) : Bool :=
  bAnd(entsK M J F 0, bAnd(Nat.ble (popK J) 8, CFSG.KC.F2Set24.strict (cntK ch36909X J F 0 0 0)
    fun n => Bool.rec (motive := fun _ => Bool) (Nat.blt 54 n) true (Nat.blt n 27)))

@[expose] noncomputable def ch36909aw : List (List (Nat × Nat × Nat)) → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ k => Nat.beq k 125)
    (fun F _ ih Js k => List.rec (motive := fun _ => Bool) false
      (fun J Js' _ => bAnd(ch36909a1 (CertificateChecks.KernelCo1FiveK.AT k) J F, ih Js' (Nat.succ k)))
      Js)

theorem ch36909a : ch36909aw FA JA 1 = true := by quickRfl

end CertificateChecks.KernelCo1Pump

end
