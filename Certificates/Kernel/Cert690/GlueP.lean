module

public import Certificates.Kernel.Cert690.GrpP
public import Certificates.Kernel.Cert690.GrpPEnum
public import Certificates.Kernel.Cert690.BaseP
public import CFSG.Certificates.Kernel.Cert690.GrpSound

public section

namespace CertificateChecks.KernelC690.GrpP

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

theorem oGens : oGensC false = [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] :=
  oWords_code_false

theorem omGens :
    omegaGensC false = [34647329153, 35704297409, 34630292097, 34630549889, 34629255234] :=
  omegaWords_code_false

theorem checks : GrpChecks false O par S Om omPar Sm inv where
  lenO := lenO
  lenOm := lenOm
  ixO := ixO
  ixOm := ixOm
  bfsO := by rw [oGens]; exact bfsO
  bfsOm := by rw [omGens]; exact bfsOm
  invO := invO
  head := by decide +kernel
  headm := by decide +kernel
  parO := by rw [oGens]; exact parO
  clO := by rw [oGens]; exact clO
  invGO := by rw [oGens]; exact invGO
  parOm := by rw [omGens]; exact parOm
  clOm := by rw [omGens]; exact clOm
  invGOm := by rw [omGens]; exact invGOm
  invMul := by rw [lenO]; exact invMul

theorem censusBaseP : censusBase false () = true :=
  censusBase_of checks (by rw [lenO]; exact transP) (by rw [lenO]; exact lsP)

end CertificateChecks.KernelC690.GrpP

end
