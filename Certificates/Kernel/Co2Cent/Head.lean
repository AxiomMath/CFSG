module

public import Certificates.Kernel.Co2Cent.Data
public import Certificates.Data.Kernel.OrbRow.Cent
public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Co2Cent
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import Certificates.Kernel.Co2I301.ChainL
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def hdK (S : List Nat) (k : Nat) (D : List (List Int)) (nb : Nat)
    (B : List Nat) : Bool :=
  invsF 2300 12 (mask 12) S fun SI =>
    headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) (getS S) (getS SI) k 2 D nb (packB 12 B)

@[expose] def dA : List (List Int) :=
  CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2ChainAWords.toList.drop 2

@[expose] def dB : List (List Int) :=
  CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2ChainBWords.toList.drop 2

@[expose] def dL : List (List Int) :=
  CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LWords.toList.drop 2

theorem ch17351_hA : hdK SA 16 dA 10 BA = true := by
  quickRfl

theorem ch17351_hB : hdK SB 17 dB 7 BB = true := by
  quickRfl

theorem ch17351_hL : hdK SL 6 dL 3 BL = true := by
  quickRfl

theorem ch17351_oAB : bAnd(Nat.beq (getS SA 0) (CertificateChecks.KernelSpor.Co2A.S 0),
    bAnd(Nat.beq (getS SA 1) (CertificateChecks.KernelSpor.Co2A.S 1),
    bAnd(Nat.beq (getS SB 0) (CertificateChecks.KernelSpor.Co2A.S 0),
    bAnd(Nat.beq (getS SB 1) (CertificateChecks.KernelSpor.Co2A.S 1),
    allN 6 (fun j => Nat.beq (getS SL j) (CertificateChecks.KernelCo2I301.CH.F (37 + j))))))) =
      true := by
  quickRfl

end CFSG.KD.Co2Cent

end
