module

public import Certificates.Kernel.Co1M.D10078
public import Certificates.Kernel.Co1M.D10078T
public import Certificates.Data.Kernel.Co1M.U6Odd
public import Certificates.Data.Kernel.Co1M.U6OddLab
public import Certificates.Kernel.VecCert.Co1.Data
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.Forms

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.U6Odd CFSG.KC.Co1M CFSG.KC.VecK CFSG.Sporadic.Co1.Module.Pairs

@[expose] noncomputable def labK78 (w : Nat) : Nat :=
  if w = 0 then 0 else if q0N w then 2 else
    if orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w then 3 else 1

theorem k78_lab : (Nat.beq (labK78 16584974) 3 && Nat.beq (labK78 (2 ^^^ 16584974)) 3) = true := by
  quickRfl

theorem k78_labT11 : labCK labK78 PV1178 LB1178 W1178 = true := by quickRfl

theorem k78_labT7 : labCK labK78 PV778 LB778 W778 = true := by quickRfl

theorem k78_labT5 : labCK labK78 PV578 LB578 W578 = true := by quickRfl

theorem k78_tup11 : tupK (labC PV1178 LB1178) W1178 2 16584974 [2, 16584974, 13392743, 15259617] 1 =
    true := by
  quickRfl

theorem k78_tup7 : tupK (labC PV778 LB778) W778 2 16584974
    [2, 16584974, 12539971, 10361096, 459969, 696249] 2 = true := by
  quickRfl

theorem k78_tup5 : tupK (labC PV578 LB578) W578 2 16584974
    [2, 16584974, 1095512, 9326441, 5595851, 4691620, 92536, 562925] 12 = true := by
  quickRfl

end CertificateChecks.KernelCo1M

end
