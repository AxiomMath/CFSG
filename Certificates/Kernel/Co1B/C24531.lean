module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreInputs
public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Co1Block.XFix
public meta import CFSG.Sporadic.Co1Block.PermData
public import Certificates.Kernel.Co1B.Chk24531
public import Certificates.Kernel.Co1B.C2041
public import Certificates.Kernel.Co1Cover.Bridge24530

public section

namespace CertificateChecks.KernelCo1B.C24531

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.Sporadic.Co1Block

theorem fixU (M : Nat) : xFixCount certVecs (CFSG.KC.Co1F2.unpackR 24 M) =
    CFSG.KC.Co1B.fixTabK (CFSG.KC.Co1F2.trK 24 M) CV.F 117 :=
  xFix_eq rfl

open Certificates in
open CFSG.EvenSporadicStandard.TwoCo1 CFSG.Sporadic.Co1Block in
theorem c24531 :
    (xFixCount certVecs eRowsA = 2280)
    ∧ (xFixCount certVecs eRowsC = 264) := by
  refine ⟨?_, ?_⟩
  · rw [KernelCo1Cover.ECore.eRowsA_eq, fixU, Nat.eq_of_beq_eq_true xA]
  · rw [KernelCo1Cover.ECore.eRowsC_eq, fixU, Nat.eq_of_beq_eq_true xC]

end CertificateChecks.KernelCo1B.C24531

end
