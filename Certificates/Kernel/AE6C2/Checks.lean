module

public import Certificates.Kernel.AE6C2.Data
public import Certificates.Data.Kernel.AE6C2T
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.AE6F CFSG.KC.AE6C2
open CertificateChecks.KernelAE6F (RG)
open CertificateChecks.KernelAE6ModC (PLL)

@[expose] noncomputable def CZIL : List (List Nat) :=
  trPL 360 9 CertificateChecks.KernelAE6Sm.CZ.LR CertificateChecks.KernelAE6Sm.CZ.TRI 5

theorem kTRZ : ((CZL.zip CZIL).all fun p => (p.1.zip p.2).all fun q =>
    permOK 360 9 (mask 9) (360 * 9) q.1 q.2) = true := by decide +kernel

theorem kFix : fixLv [] CZL BZ = true := by decide +kernel

@[expose] noncomputable def TLP : List (List Nat) :=
  trPL 360 9 KernelAE6Core.PL.LR KernelAE6Core.PL.TR 4

theorem kBasicT : basicT RG PLL (TLP.getD 0 []) (TLP.getD 1 []) (TLP.getD 2 []) (TLP.getD 3 [])
    L3I BZ CZL = true := by quickRfl

theorem kSearch : treeN GTN TGN ZCN LSP = true := by decide +kernel

end CertificateChecks.KernelAE6C2

end
