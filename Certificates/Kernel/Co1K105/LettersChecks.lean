module

public import Certificates.Data.Kernel.Co1K105.LettersK
public import Certificates.Data.Kernel.Co1K105.Letters
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Kernel.Co1B.Dag2044
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Co1K105

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CertificateChecks.KernelCo1Cover CFSG.KD.Co1B
  CertificateChecks.KernelCo1B.C2044

@[expose] noncomputable def lkCc : Nat :=
  lkC R0 lkAI (getL oneK E 0) (getL oneK E 1) (getL oneK IRS 23)

@[expose] noncomputable def lkQP : Nat := lkPack lkQL

theorem lk_head : lkHead R0 lkAI (getL oneK E 0) (getL oneK E 1) (getL oneK IRS 23) lkCI = true := by
  quickRfl

theorem lk_rows : lkRows (getL oneK IRS 23) lkQG lkQL 0 = true := by quickRfl

theorem lk_dist : lkDist lkQL = true := by quickRfl

theorem lk_gens : lkGens lkQG lkQL = true := by quickRfl

theorem lk_e0 : lkLetter lkQP (lkGetLL letters 0) (lkG lkCc lkCI (getL oneK E 0))
    (lkG lkCc lkCI (getL oneK E 0)) = true := by quickRfl

theorem lk_e1 : lkLetter lkQP (lkGetLL letters 1) (lkG lkCc lkCI (getL oneK E 1))
    (lkG lkCc lkCI (getL oneK E 1)) = true := by quickRfl

theorem lk_e2 : lkLetter lkQP (lkGetLL letters 2) (lkG lkCc lkCI (getL oneK E 2))
    (lkG lkCc lkCI (getL oneK E 2)) = true := by quickRfl

theorem lk_e3 : lkLetter lkQP (lkGetLL letters 3) (lkG lkCc lkCI (getL oneK E 3))
    (lkG lkCc lkCI (getL oneK E 3)) = true := by quickRfl

theorem lk_e4 : lkLetter lkQP (lkGetLL letters 4) (lkG lkCc lkCI (getL oneK E 4))
    (lkG lkCc lkCI (getL oneK E 4)) = true := by quickRfl

theorem lk_e5 : lkLetter lkQP (lkGetLL letters 5) (lkG lkCc lkCI (getL oneK E 5))
    (lkG lkCc lkCI (getL oneK E 5)) = true := by quickRfl

theorem lk_e6 : lkLetter lkQP (lkGetLL letters 6) (lkG lkCc lkCI (getL oneK E 6))
    (lkG lkCc lkCI (getL oneK E 6)) = true := by quickRfl

theorem lk_e7 : lkLetter lkQP (lkGetLL letters 7) (lkG lkCc lkCI (getL oneK E 7))
    (lkG lkCc lkCI (getL oneK E 7)) = true := by quickRfl

theorem lk_e8 : lkLetter lkQP (lkGetLL letters 8) (lkG lkCc lkCI (getL oneK E 8))
    (lkG lkCc lkCI (getL oneK E 8)) = true := by quickRfl

theorem lk_e9 : lkLetter lkQP (lkGetLL letters 9) (lkG lkCc lkCI (getL oneK E 9))
    (lkG lkCc lkCI (getL oneK E 9)) = true := by quickRfl

theorem lk_e10 : lkLetter lkQP (lkGetLL letters 10) (lkG lkCc lkCI (getL oneK E 10))
    (lkG lkCc lkCI (getL oneK E 10)) = true := by quickRfl

theorem lk_w0 : lkLetter lkQP (lkGetLL letters 11)
    (lkG lkCc lkCI (lkWord R4 R5 (lkPair lkCodes 0).1 (lkPair lkCodes 0).2))
    (lkG lkCc lkCI (getL oneK lkWI 0)) = true := by quickRfl

theorem lk_w1 : lkLetter lkQP (lkGetLL letters 12)
    (lkG lkCc lkCI (lkWord R4 R5 (lkPair lkCodes 1).1 (lkPair lkCodes 1).2))
    (lkG lkCc lkCI (getL oneK lkWI 1)) = true := by quickRfl

theorem lk_w2 : lkLetter lkQP (lkGetLL letters 13)
    (lkG lkCc lkCI (lkWord R4 R5 (lkPair lkCodes 2).1 (lkPair lkCodes 2).2))
    (lkG lkCc lkCI (getL oneK lkWI 2)) = true := by quickRfl

theorem lk_w3 : lkLetter lkQP (lkGetLL letters 14)
    (lkG lkCc lkCI (lkWord R4 R5 (lkPair lkCodes 3).1 (lkPair lkCodes 3).2))
    (lkG lkCc lkCI (getL oneK lkWI 3)) = true := by quickRfl

theorem lk_h : lkLetter lkQP (lkGetLL letters 15) (mulWK (mulWK (D2.M 0) (D2.M 7)) (D2.M 4))
    (mulWK (mulWK (D2.MI 4) (D2.MI 7)) (D2.MI 0)) = true := by quickRfl

theorem lk_b0 : lkLetter lkQP (lkGetLL letters 16) (D2.M 0) (D2.MI 0) = true := by quickRfl

end CFSG.KD.Co1K105

end
