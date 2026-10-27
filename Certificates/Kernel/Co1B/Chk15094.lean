module

public import Certificates.Kernel.Co1B.Chk2047
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BFix
public import Certificates.Data.Co1HoltFreeTwoC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C15094

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KC.Co1F2 CFSG.KC.Co1B
open CertificateChecks.KernelCo1B.C2047
open CFSG.ComponentClassification.RankTwoExceptional.HoltFree

@[expose] noncomputable def PP : Nat := mulWK (D2.M Data.pIdx.1) (D2.M Data.pIdx.2)

@[expose] noncomputable def WK (q : Nat) : Nat := mulWK q (mulWK (mulWK PP q) (powWK PP 10))

@[expose] noncomputable def AK : Nat := WK (QM Data.aIdx)

@[expose] noncomputable def BK : Nat := WK (QM Data.bIdx)

@[expose] noncomputable def FK : Nat := WK (QM Data.fIdx)

theorem xO : (Nat.beq (powWK PP 11) oneK && (unpack 24 24 PP != unpack 24 24 oneK)) = true := by
  quickRfl

theorem xFix : allN 2048 (fun i => !(unpack 24 24 (mulWK PP (QT.P i)) ==
    unpack 24 24 (mulWK (QT.P i) PP)) || unpack 24 24 (QT.P i) == unpack 24 24 idM ||
    unpack 24 24 (QT.P i) == unpack 24 24 IC) = true := by
  quickRfl

theorem xA : Nat.beq (fixTabK (trK 24 AK) CV.F 117) 2280 = true := by quickRfl
theorem xB : Nat.beq (fixTabK (trK 24 BK) CV.F 117) 264 = true := by quickRfl
theorem xBC : Nat.beq (fixTabK (trK 24 (mulWK BK IC)) CV.F 117) 264 = true := by quickRfl
theorem xF : Nat.beq (fixTabK (trK 24 FK) CV.F 117) 2280 = true := by quickRfl
theorem xAF : Nat.beq (fixTabK (trK 24 (mulWK AK FK)) CV.F 117) 2280 = true := by quickRfl

end CertificateChecks.KernelCo1B.C15094

end
