module

public import Certificates.Kernel.CosetJ.J4Checks
public import CFSG.Certificates.Kernel.CosetJ.F2CertSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCosetJ.J4

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.J4Schreier CFSG.Sporadic.Recognition.J4Multiplier
  CFSG.KC.CosetJ.F2

theorem ws_eq : (List.finRange 6).map wordsPos = ws := by decide +kernel

theorem foxCert : J4FoxCert := by
  have h := foxOK_sound (X := j4FoxX) (Y := j4FoxY) (a := xColumns) (b := yColumns)
    (by rw [ws_eq]; exact fox_check)
  have e : j4FoxMat = Matrix.of fun (r : Fin 6 × Fin 11) (c : Fin (11 + 11)) =>
      flat (foxVec (colsMatrix xColumns) (colsMatrix yColumns) (wordsPos r.1)
        (Pi.single r.2 1)) c := by
    ext r c
    exact j4FoxMat_apply r c
  rw [J4FoxCert, e]
  exact h

theorem formCert : J4FormCert := formOK_sound form_check

end CertificateChecks.KernelCosetJ.J4

end
