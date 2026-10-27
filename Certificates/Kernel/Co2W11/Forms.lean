module

public import Certificates.Data.Kernel.F2FormId
public import Certificates.Kernel.Co2W11.FormsData
public import Certificates.Kernel.Co2W11.Sep
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2W11

open CFSG.KC.F2FormId CFSG.KC.F2TriSep CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KLie.CT
  CertificateChecks.KernelLC.Co2Ops

@[expose] noncomputable def polF (Q : Nat) : Nat := Nat.xor Q (trK 22 Q)

theorem invQ_ok : (invQK 22 Fm.Q SA.M && invQK 22 Fm.Q SB.M) = true := by quickRfl

theorem nondeg_ok : Nat.beq (mulW 22 (polF Fm.Q) Fm.Finv) (idF 22) = true := by quickRfl

theorem nofix_ok : Nat.beq (fixSumK 22 [(SA.M, Fm.X1), (SB.M, Fm.X2)]) (idF 22) = true := by
  quickRfl

theorem fixH0_ok :
    (Nat.beq (vmF 22 (trK 22 (polF Fm.Q)) 40) Fm.lam && bit Fm.lam Fm.p &&
      Nat.beq (fixSumK 22 ((gensOf S0.words).zip Fm.Xs))
        (Nat.xor (idF 22) (Nat.shiftLeft Fm.lam (Nat.mul 22 Fm.p)))) = true := by
  quickRfl

end CertificateChecks.KernelCo2W11

end
