module

public import Certificates.Kernel.Co1B.Data17330P
public import Certificates.Kernel.Co1B.Data17330
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.TabCo1ThreeB
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17330

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB
open CertificateChecks.KernelCo1B.Bound17591 (XB)

theorem kCFs : decide (KP.CFs = (List.range 14).map fun i =>
    storeSel 3 XB K.T (base.take i) (base.getD i 0) (conds.getD i []) (KP.Sel.getD i [])) = true := by
  quickRfl

theorem kCFs2 : decide (KP.CFs2 = (List.range 3).map fun i =>
    storeSel 12 XB K.T2 (base2.take i) (base2.getD i 0) (conds2.getD i []) (KP.Sel2.getD i [])) =
    true := by
  quickRfl

theorem kNs : (Nat.beq KP.CNs.length 14 && allN 14 fun i => memK XB (base.getD i 0) &&
    Nat.beq (KP.CNs.getD i []).length 9 && Nat.ble (KP.CNs.getD i []).sum (cnts.getD i 0)) = true := by
  quickRfl

theorem kNs2 : (Nat.beq KP.CNs2.length 3 && allN 3 fun i => memK XB (base2.getD i 0) &&
    Nat.beq (KP.CNs2.getD i []).length 9 && Nat.ble (KP.CNs2.getD i []).sum (cnts2.getD i 0)) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17330

end
