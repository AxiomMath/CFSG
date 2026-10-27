module

public import Certificates.Kernel.AE6Core.Checks
public import Certificates.Data.Kernel.AE6ModCN
public import Certificates.Data.AE6ModelC
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

#kc_fun_arg_chars CertificateChecks.KernelAE6ModC.C3W Certificates.AE6Model.c3Words
#kc_fun_arg_chars CertificateChecks.KernelAE6ModC.C1W Certificates.AE6Model.c1Words
#kc_fun_arg_chars CertificateChecks.KernelAE6ModC.C1IW Certificates.AE6Model.c1iWords

namespace CertificateChecks.KernelAE6ModC

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.AE6F CFSG.KC.AE6Core
  CFSG.KC.AE6ModC Certificates.AE6Model
open CertificateChecks.KernelAE6F (RG WL)

@[expose] noncomputable def PLL : List Nat :=
  pfilterProducts 360 9 (fun _ => true)
    (trPL 360 9 KernelAE6Core.PL.LR KernelAE6Core.PL.TR 4) (pidn 360 9) []

theorem kToks3 : toksOKw C3W.chars = true := by decide +kernel

theorem kToks1 : toksOKw C1W.chars = true := by decide +kernel

theorem kToks1i : toksOKw C1IW.chars = true := by decide +kernel

theorem kTRP : (trPL 360 9 KernelAE6Core.PL.LR KernelAE6Core.PL.TR 4).all (fun L => L.all fun t =>
    permOK 360 9 (mask 9) (360 * 9) t (pinv 360 9 t)) = true := by decide +kernel

theorem kC3 : c3N RG WL PLL (cwN C3W.chars) = true := by decide +kernel

theorem kC1 : c1N RG PLL (cwN C1W.chars) = true := by decide +kernel

theorem kC1i : c1iN RG PLL (cwN C1IW.chars) = true := by decide +kernel

theorem kC3Neg : c3N RG WL PLL.dropLast [] = false := by decide +kernel

theorem kC1Neg : c1N RG PLL ([] :: (cwN C1W.chars).tail) = false := by decide +kernel

theorem kC1iNeg : c1iN RG PLL ([] :: (cwN C1IW.chars).tail) = false := by decide +kernel

end CertificateChecks.KernelAE6ModC

end
