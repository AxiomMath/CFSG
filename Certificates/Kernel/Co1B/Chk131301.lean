module

public import Certificates.Kernel.Co1B.Tabs131301
public import Certificates.Kernel.Co1B.Text131301
public import Certificates.Data.Kernel.Co1BS0
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.S0131301

open CFSG.KC.Co1BS0 CFSG.KC.Co1B CFSG.KLie.CT

theorem kGood : (goodNl OT.chars && goodNl PT.chars && goodNl LT.chars) = true := by quickRfl
theorem kInv : (eqK (mulWK (RG 1) (RG 2)) oneK && eqK (RG 2) (mulWK (RG 1) (RG 1))) = true := by
  quickRfl
theorem kOps : (Nat.beq (pairsL (numsNl OT.chars)).length 1153 &&
    opsK RG (pairsL (numsNl OT.chars)) 0) = true := by quickRfl
theorem kPar : (Nat.beq (pairsL (numsNl PT.chars)).length 19683 &&
    parK RG EG (pairsL (numsNl PT.chars)) 0) = true := by quickRfl
theorem kE0 : eqK (EG 0) oneK = true := by quickRfl
theorem kLeft : (Nat.beq (numsNl LT.chars).length 59049 && leftK RG EG (numsNl LT.chars) 0) = true := by
  quickRfl
theorem kSort : sortK EG SG = true := by quickRfl

theorem kK0 : killK EG WG 0 1024 = true := by quickRfl
theorem kK1 : killK EG WG 1024 1024 = true := by quickRfl
theorem kK2 : killK EG WG 2048 1024 = true := by quickRfl
theorem kK3 : killK EG WG 3072 1024 = true := by quickRfl
theorem kK4 : killK EG WG 4096 1024 = true := by quickRfl
theorem kK5 : killK EG WG 5120 1024 = true := by quickRfl
theorem kK6 : killK EG WG 6144 1024 = true := by quickRfl
theorem kK7 : killK EG WG 7168 1024 = true := by quickRfl
theorem kK8 : killK EG WG 8192 1024 = true := by quickRfl
theorem kK9 : killK EG WG 9216 1024 = true := by quickRfl
theorem kK10 : killK EG WG 10240 1024 = true := by quickRfl
theorem kK11 : killK EG WG 11264 1024 = true := by quickRfl
theorem kK12 : killK EG WG 12288 1024 = true := by quickRfl
theorem kK13 : killK EG WG 13312 1024 = true := by quickRfl
theorem kK14 : killK EG WG 14336 1024 = true := by quickRfl
theorem kK15 : killK EG WG 15360 1024 = true := by quickRfl
theorem kK16 : killK EG WG 16384 1024 = true := by quickRfl
theorem kK17 : killK EG WG 17408 1024 = true := by quickRfl
theorem kK18 : killK EG WG 18432 1024 = true := by quickRfl
theorem kK19 : killK EG WG 19456 227 = true := by quickRfl

end CertificateChecks.KernelCo1B.S0131301

end
