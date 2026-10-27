module

public import Certificates.Kernel.Co1FiveComp.Data
public import Certificates.Kernel.Co1FiveK.Chk
public import Certificates.Data.Kernel.Co1FiveComp
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveComp

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1FiveK Timmesfeld.Co1Five
  Timmesfeld.Co1FiveComp CertificateChecks.KernelCo1FiveK

@[expose] noncomputable def B1 : Nat := a0K DK (repA.getD 1 0)

@[expose] noncomputable def B2 : Nat := a0K DK (repB.getD 1 0)

theorem c10145kD0 :
    bindListK 24 24 B1 CFSG.HardMathSupport.Dickson.I271.TabCo1.repD0.toList = true := by
  quickRfl

theorem c10145kMem :
    allN 3 (fun j => (List.range 625).any fun i => Nat.beq (QT.P i) (DK j)) = true := by
  quickRfl

theorem c10145kCen : cenK AT (QM 1) = true := by quickRfl

theorem c10145kSTN : Nat.beq ST.N 60 = true := by quickRfl

theorem c10145kST : gtPinK (SG D.M D.MI) 5 100000 ST.N ST.P ST.PAR ST.LAB ST.W ST.S = true := by
  quickRfl

theorem c10145kPerf : allN 5 (compKAt D.M D.MI B1 B2) = true := by quickRfl

end CertificateChecks.KernelCo1FiveComp

end
