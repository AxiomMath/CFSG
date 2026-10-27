module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.Sporadic.SmallOddCore.LocalSpec
import Certificates.Kernel.Census.J2H.Facts
import Certificates.Kernel.Census.J2H.Checks
import Certificates.Kernel.Census.J2H.Count
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
import Certificates.Data.CFSGNative.J2.Certificate
import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelNative
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace Certificates

open CertificateChecks.KernelJ2H

open CFSG.ComponentClassification.HarrisLit.EndB CFSG.ComponentClassification.J2Cover
  CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem certificate22400 : (∃ x y : Equiv.Perm (Fin 315), x ∈ centralizerIn P permTwoA ∧
      y ∈ centralizerIn P permTwoA ∧ orderOf x = 5 ∧ orderOf y = 5 ∧
      Subgroup.closure {x, y} = centralizerIn P permTwoA) ∧
    (∃ S₀ : Subgroup (Equiv.Perm (Fin 315)), S₀ ≤ centralizerIn P permTwoA ∧
      Nat.card S₀ = 128 ∧ permTwoA ∈ S₀ ∧
      Nat.card ↥(centralizerIn R permTwoA ⊓
        Subgroup.centralizer (S₀ : Set (Equiv.Perm (Fin 315)))) = 2) ∧
    (∃ G : Subgroup (Equiv.Perm (Fin 315)), G ≤ centralizerIn P permA ∧ Nat.card G = 60 ∧
      ⁅G, G⁆ = G) ∧
    Nat.card ↥(centralizerIn R permTwoA ⊓ Subgroup.centralizer
      (genOf 315 ([[1, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 1], [1, 1, 2, 2, 1, 1, 2, 2],
        [1, 2, 2, 1, 1, 2, 2, 1]].map (wordTbl 315 c2AGens)) : Set (Equiv.Perm (Fin 315)))) = 2 :=
  ⟨odd_gens, s0_facts, a5_facts, v_facts⟩

end Certificates
