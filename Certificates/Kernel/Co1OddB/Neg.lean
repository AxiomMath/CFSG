module

public import Certificates.Data.Kernel.Co1FixList
public import Certificates.Data.Kernel.Co1OddB
public import Certificates.Kernel.Co1B.Data2046
public import Certificates.Kernel.Co1OddB.Data

public section

namespace CertificateChecks.KernelCo1OddB

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.F2W CFSG.KC.Co1OddB CFSG.KC.Co1Fix CFSG.KC.M1F2
  CFSG.Sporadic.Co1Schreier

theorem neg_prog : progK 24 (RB.set 9 (RB.getD 14 0)) Data.oddBProg 3 = false := by decide +kernel

theorem neg_fixList : fixListK YT YT FY W.dropLast = false := by decide +kernel

theorem neg_cand : candK (RB.getD 9 0) (RB.getD 14 0) CFSG.KD.Co1B.SBK HP BT oneK (W.getD 1 0)
    (W.getD 2 0) = false := by decide +kernel

theorem neg_order : eqK (powWK (RB.getD 9 0) 2) oneK = false := by decide +kernel

end CertificateChecks.KernelCo1OddB

end
