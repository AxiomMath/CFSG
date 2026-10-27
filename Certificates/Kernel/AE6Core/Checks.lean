module

public import Certificates.Kernel.AE6Core.Chain
public import Certificates.Kernel.AE6F.Checks
public import Certificates.Kernel.Misc.ArgCharsFun
public import Certificates.Data.Kernel.AE6Core
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

#kc_fun_arg_chars CertificateChecks.KernelAE6Core.CW Certificates.AE6Model.cWords

namespace CertificateChecks.KernelAE6Core

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.AE6Tri CFSG.KC.AE6Core
  Certificates.AE6Model
open CertificateChecks.KernelAE6F (RG)

theorem kToks : toksOKw CW.chars = true := by decide +kernel

theorem kToksNeg : (!toksOKw ('x' :: CW.chars)) = true := by decide +kernel

theorem kLen : Nat.beq (cwN CW.chars).length 4 = true := by decide +kernel

theorem kInv : invOKN RG = true := by decide +kernel

theorem kComm : commAllN RG zWord (cwN CW.chars) = true := by decide +kernel

theorem kPL : plOK RG (cwN CW.chars) PL.S = true := by decide +kernel

theorem kCommNeg : (!commAllN RG (kWords.getD 0 []) [(cwN CW.chars).getD 1 []]) = true := by
  decide +kernel

theorem kPLNeg : (!plOK RG [[], ((cwN CW.chars).getD 1 []).tail] PL.S) = true := by
  decide +kernel

end CertificateChecks.KernelAE6Core

end
