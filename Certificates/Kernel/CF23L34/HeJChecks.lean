module

public import Certificates.Kernel.CF23L34.HeJData
public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Data.Kernel.CF23L34.HeJ
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeJ

open CFSG.KC.Enum CFSG.KS CFSG.KC.CF23L34 CertificateChecks.KernelLC.HeFix
open CFSG.ComponentClassification.GSThmB.CF23L34 CFSG.LieType.Multipliers.L34

theorem ch22226_gen : (Nat.beq (HeJT 0) (HG.F 0) && Nat.beq (HeJT 2) (HG.F 1)) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeJ

#kc_each CertificateChecks.KernelLC.HeJ ch22226i_
  (fun i => CFSG.KC.CF23L34.hjInvOK CertificateChecks.KernelLC.HeJT
    (CFSG.KC.CF23L34.hjInvJ.getD i 0)) 0 10

#kc_each CertificateChecks.KernelLC.HeJ ch22226t_
  (CFSG.KC.CF23L34.hjTabOK CertificateChecks.KernelLC.HeJT) 0 15

#kc_each CertificateChecks.KernelLC.HeJ ch22226w_
  (fun i => CFSG.KC.CF23L34.hjEqB CertificateChecks.KernelLC.HeJT
    (CFSG.KC.CF23L34.hjCw (CFSG.KC.CF23L34.hjRelW.getD i [])) []) 0 21

#kc_each CertificateChecks.KernelLC.HeJ ch22226l_
  (fun i => CFSG.KC.CF23L34.hjLabK CertificateChecks.KernelLC.HeJT
    (CFSG.ComponentClassification.GSThmB.CF23L34.hjLabels.getD i (0, 0, 0, 0))) 0 3

namespace CertificateChecks.KernelLC.HeJ

open CFSG.KC.Enum CFSG.KS CFSG.KC.CF23L34 CertificateChecks.KernelLC.HeFix
open CFSG.ComponentClassification.GSThmB.CF23L34 CFSG.LieType.Multipliers.L34

theorem ch22226_comm : (hjEqB HeJT [250, 1] [1, 250] && hjEqB HeJT [277, 1] [1, 277] &&
    hjEqB HeJT [32, 1] [1, 32]) = true := by
  quickRfl

theorem ch22226_z : (hjEqB HeJT (hjCw zTwo) [1] &&
    hjEqB HeJT (hjCw zOne ++ hjCw zOne) []) = true := by
  quickRfl

theorem ch22226_ne : (hjNeAt HeJT (hjCw zOne) [] 0 && hjNeAt HeJT (hjCw zOne) [1] 0 &&
    hjNeAt HeJT [250, 277] [277, 250] 0 &&
    hjNeAt HeJT (32 :: hjCw zOne) (hjCw zOne ++ [32]) 1) = true := by
  quickRfl

theorem ch22226_len : hjRelW.length = 21 ∧ hjInvJ.length = 10 ∧ hjKeep.length = 15 ∧
    hjLabels.length = 3 := by
  decide +kernel

theorem ch22226n_rel :
    bIf(hjEqB HeJT (hjCw ((hjRelW.getD 0 []).drop 1)) [], false, true) = true := by
  quickRfl

theorem ch22226n_comm :
    bIf(hjEqB HeJT (32 :: hjCw zOne) (hjCw zOne ++ [32]), false, true) = true := by
  quickRfl

theorem ch22226n_lab : bIf(hjEqB HeJT (hjX 313 ++ [2]) (2 :: (hjCw (CFSG.ComponentClassification.GrSLit.L34Facts.tw 4) ++
    hjCw zOne ++ hjX 313)), false, true) = true := by
  quickRfl

theorem ch22226n_tab :
    bIf(Nat.beq (wzK 8330 14 HeJT hjIdx (hjD 86)) (HeJT 4), false, true) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeJ

end
