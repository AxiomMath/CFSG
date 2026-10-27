module

public import Certificates.Data.GrSLitL34SuzStdOddLeafRootPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuter
import Certificates.Kernel.Sporadic.OddCore.Suz786002

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.GrSLit.L34Sec5S in
theorem certificate786002 :     (∀ j < 2, suzRootPerm j * repPerm 6 = repPerm 6 * suzRootPerm j ∧ suzRootPerm j ^ 4 = 1) ∧
      ∀ (τ : Equiv.Perm (Fin 1782))
        (hτ : τ ∈ suzT ⊓ Subgroup.centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782)))),
        (∀ j < 2, rhoHat ⟨τ, hτ⟩ * suzRootPerm j = suzRootPerm j * rhoHat ⟨τ, hτ⟩) →
          ∃ hτE : τ ∈ invE 0, rho0 ⟨τ, hτE⟩ ∈ suzD :=
  KernelSpor.Suz786002.check786002

end Certificates
