module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenBase
import Certificates.Certificate2043
import Certificates.Certificate3024
import Certificates.Kernel.Co1SevenK.GlueB

public section

namespace Certificates

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S in
theorem certificate13698 : Nat.card (Subgroup.centralizer ({tE} : Set ↥GA)) = 1176 ∧
    gE 70 ∈ Subgroup.centralizer ({tE} : Set ↥GA) ∧
    CFSG.Open.GLAPPrimeCoreOf 7 (Subgroup.centralizer ({tE} : Set ↥GA)) = ⊥ ∧
    MRep (Timmesfeld.Co1Seven.rowAt (Timmesfeld.Co1Seven.gDag Native.aR Native.bR).1
      Timmesfeld.Co1Seven.iT) ((tE : ↥GA) : GL24) := by
  obtain ⟨h1, h2, h3⟩ := CertificateChecks.KernelCo1SevenK.factsB
  exact ⟨h1, h2, h3, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.rep_gE
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.sylowOK_parts
      CertificateChecks.KernelCo1SevenK.sylowOK_K).1 _⟩

end Certificates
