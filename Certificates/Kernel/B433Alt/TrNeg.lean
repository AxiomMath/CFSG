module

public import Certificates.Kernel.B433Alt.TrOK

public section

namespace CertificateChecks.KernelB433.TrNeg

open CFSG.KC.B4A

theorem trneg_start : trOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW 5965
    (CFSG.KD.B4AT.K0.getD 0 0) (wMk 16777216 0) (CFSG.KD.B4AT.trWord 1)
    (CFSG.KD.B4AT.J.getD 0 0) (CFSG.KD.B4AT.K1.getD 0 0) (CFSG.KD.B4AT.A1.getD 0 0) = false := by
  decide +kernel

theorem trneg_letter : wsFail (trL CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW 5965 0
    (wsMk 0 0 0, wMk 16777216 0)).1 = 1 := by
  decide +kernel

end CertificateChecks.KernelB433.TrNeg

end
