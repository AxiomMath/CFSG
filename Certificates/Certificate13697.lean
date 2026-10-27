module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenBase
import Certificates.Certificate2043
import Certificates.Certificate3024
import Certificates.Kernel.Co1SevenK.GlueA

public section

namespace Certificates

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S in
theorem certificate13697 : Nat.card (Subgroup.centralizer ({sE} : Set ↥GA)) = 17640 ∧
    gE 68 ∈ Subgroup.centralizer ({sE} : Set ↥GA) ∧
    gE 69 ∈ Subgroup.centralizer ({sE} : Set ↥GA) ∧
    CFSG.Open.GLAPPrimeCoreOf 7 (Subgroup.centralizer ({sE} : Set ↥GA)) = ⊥ ∧
    (∀ c ∈ Subgroup.centralizer ({sE} : Set ↥GA), c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.tE = CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.tE * c → c ^ 7 = 1) ∧
    MRep (Timmesfeld.Co1Seven.rowAt (Timmesfeld.Co1Seven.gDag Native.aR Native.bR).1
      Timmesfeld.Co1Seven.iS) ((sE : ↥GA) : GL24) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := CertificateChecks.KernelCo1SevenK.factsA
  exact ⟨h1, h2, h3, h4, h5, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.rep_gE
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.sylowOK_parts
      CertificateChecks.KernelCo1SevenK.sylowOK_K).1 _⟩

end Certificates
