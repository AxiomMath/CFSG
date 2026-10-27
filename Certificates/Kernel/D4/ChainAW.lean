module

public import Certificates.Kernel.D4.ChainAD
public import Certificates.Data.Kernel.Spor.RawSch3G
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4.CA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] def pT1 : Nat := nat_lit 197122

@[expose] def pJ1 : Nat := nat_lit 12918653444

@[expose] def wd1 : List (List Nat) :=
  [[0], [1], [1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0]]

theorem inv1 : invTabK 8 (stepsAt 2457 12 S 8 BP 1) = true := by quickRfl

theorem tsb1 : allN (stCnt pT1) (fun a => Nat.blt (stAt pT1 a) 8) = true := by quickRfl

theorem tj1 : incK pJ1 pT1 = true := by quickRfl

theorem wds1 : wdsK 2457 12 (mask 12) (pidn 2457 12) S SI 8 pJ1 wd1 2 = true := by quickRfl

theorem lo1 : allN (stCnt (stepsAt 2457 12 S 8 BP 1))
    (fun j => Nat.ble 2 (stAt (stepsAt 2457 12 S 8 BP 1) j)) = true := by quickRfl

@[expose] noncomputable def s1f (s : Nat) : Bool :=
  schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI 8 BP 7 1 pT1 (s * 16) 16

end CertificateChecks.KernelD4.CA

end
