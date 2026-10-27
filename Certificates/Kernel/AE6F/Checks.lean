module

public import Certificates.Kernel.AE6F.Chain
public import Certificates.Kernel.OmegaEight.AutChainAP
public import Certificates.Data.Kernel.AE6FN
public import Certificates.Data.Kernel.KGC31PB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6F

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.AE6F Certificates.AE6Model

@[expose] noncomputable def RG : List Nat := (List.range 8).map CertificateChecks.KernelO8.AP.S

@[expose] noncomputable def WL : List Nat :=
  pfilterProducts 360 9 (fun _ => true) (trPL 360 9 W.LR W.TR 1) (pidn 360 9) []

theorem kGensW : (List.range 5).all (fun j => Nat.beq (W.S j) (awN RG (wWords.getD j []))) =
    true := by decide +kernel

theorem kTRW : (trPL 360 9 W.LR W.TR 1).all (fun L => L.all fun t =>
    permOK 360 9 (mask 9) (360 * 9) t (pinv 360 9 t)) = true := by decide +kernel

theorem kBasic : fBasicN RG = true := by decide +kernel

theorem kTwin : fTwinChecksN RG = true := by decide +kernel

theorem kCyc : fCycChecksN RG = true := by decide +kernel

theorem kDiag : fDiagChecksN RG WL = true := by decide +kernel

theorem kDiagNeg : fDiagChecksN RG [] = false := by decide +kernel

theorem kBasicNeg : fBasicN ((RG.set 0 (RG.getD 2 0)).set 2 (RG.getD 0 0)) = false := by
  decide +kernel

end CertificateChecks.KernelAE6F

end
