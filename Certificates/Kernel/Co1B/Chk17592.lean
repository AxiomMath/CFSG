module

public import Certificates.Kernel.Co1B.Data17592
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.TabCo1ThreeDRoot
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17592

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot
open CertificateChecks.KernelCo1B.Bound17591 (XB)

@[expose] noncomputable def RR : Nat := CertificateChecks.KernelCo1ThreeK.R.M 2

theorem kT : (Nat.beq KD.T.length 3 &&
    allN 3 fun i => eqK (getL 0 KD.T i) (trK 24 (powWK RR i))) = true := by quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 8 && Nat.blt s.2 3) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotKn 3 KD.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kCFs : decide (KD.CFs = (List.range 8).map fun i =>
    storeSel 3 XB KD.T (base.take i) (base.getD i 0) (conds.getD i []) (KD.Sel.getD i [])) = true := by
  quickRfl

theorem kNs : (Nat.beq KD.CNs.length 8 && allN 8 fun i => memK XB (base.getD i 0) &&
    Nat.beq (KD.CNs.getD i []).length 9 && Nat.ble (KD.CNs.getD i []).sum (cnts.getD i 0)) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17592

end
