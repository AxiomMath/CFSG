module

public import Certificates.Kernel.Cert690.GrpM
public import Certificates.Kernel.Cert690.GrpMEnum
public import Certificates.Kernel.Cert690.BaseM
public import CFSG.Certificates.Kernel.Cert690.GrpSound

public section

namespace CertificateChecks.KernelC690.GrpM

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

theorem oGens : oGensC true = [35721076609, 35720809665, 35704292801, 35704030401, 17717821506] :=
  oWords_code_true

theorem omGens :
    omegaGensC true = [35721076609, 35720809665, 35704292801, 35704030401, 17718853698] :=
  omegaWords_code_true

theorem checks : GrpChecks true O par S Om omPar Sm inv where
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

theorem censusBaseM : censusBase true () = true :=
  censusBase_of checks (by rw [lenO]; exact transM) (by rw [lenO]; exact lsM)

end CertificateChecks.KernelC690.GrpM

end
