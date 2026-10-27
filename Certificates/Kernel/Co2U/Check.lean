module

public import Certificates.Data.Kernel.Co2U.Twin
public import Certificates.Kernel.Co2U.Data
public import Certificates.Kernel.LocalComp.Co2Ops

public section

namespace CertificateChecks.KernelCo2U

open CFSG.KC.Co2U CFSG.KC.Co2Smith CFSG.KC.Co2InvS CFSG.GF2W1112 CertificateChecks.KernelLC.Co2Ops

theorem ch38957w_ : wordsK SA.M SB.M W.chars EltP.P = true := by decide +kernel

theorem ch38957len_ : EltP.P.length = 33 := by decide +kernel

theorem ch38957a_ :
    eqCheckK EltP.P (w12UOrdEqs () ++ w12UCommEqs () ++ w12UConjEqs ()) = true := by
  decide +kernel

theorem ch38957e_ : eqK (EltP.P.getD 0 0) IDP = false := by decide +kernel

theorem ch38958a_ : eqCheckK EltP.P (w12UDecEqs ()) = true := by decide +kernel

end CertificateChecks.KernelCo2U

end
