module

public import Certificates.Kernel.Co1Nine.Tabs
public import Certificates.Data.Kernel.Co1Nine.Defs
public import Certificates.Kernel.Co1P.Chk21158
public import CFSG.Sporadic.Co1Patterson.IndexNineInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo1Nine

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Co1Nine
open CFSG.KC.Co1B (eqK mulWK oneK)
open CertificateChecks.KernelCo1P (BK BIK AL ypW qwW)
open CFSG.Sporadic.Co1Patterson.IndexNine CFSG.Sporadic.Co1Patterson.TwistNative

@[expose] noncomputable def brayK (m : List Nat) (l : Nat) : Bool :=
  (fun B BI => andB (eqK (mulWK B BI) oneK) (allN 8 fun k =>
    (fun x => orB (eqK x (ypW (m.getD k 0))) (eqK x (mulWK (ypW (m.getD k 0)) AL)))
      (mulWK (mulWK B (qwW (yBits.getD k 0))) BI)))
    (CFSG.KC.Co1F2.getL 0 BK l) (CFSG.KC.Co1F2.getL 0 BIK l)

theorem bray_chk : allN 8 (fun l => brayK (MCols.getD l []) l) = true := by quickRfl

theorem keys_chk : (MKL = MCols.map co1RowsKeyC ∧ UKL = UCols.map co1RowsKeyC ∧
    (MCols ++ UCols).all (fun m => m.length == 8 && m.all (· < 256)) ∧
    UCols = co1UWords.map (co1WordC MCols)) := by decide +kernel

theorem xy_chk : co1XYCheckC (co1WordC MCols co1XWord) (co1WordC MCols co1YWord) = true := by
  decide +kernel

theorem f_tree : allN 4725 (treeAt actF baseF MG 8 FE FPA) = true := by quickRfl
theorem f_sort : allN 4725 (sortAt 4725 FE FSG) = true := by quickRfl
theorem f_closed : allN 4725 (closedAt actF MG 8 4725 FE FCT) = true := by quickRfl
theorem f_fix : allN 4725 (fixAt FE) = true := by quickRfl

theorem u_tree : allN 4096 (treeAt mulC idK UG 4 UE UPA) = true := by quickRfl
theorem u_sort : allN 4096 (sortAt 4096 UE USG) = true := by quickRfl
theorem u_closed : allN 4096 (closedAt mulC UG 4 4096 UE UCT) = true := by quickRfl

end CertificateChecks.KernelCo1Nine

end
