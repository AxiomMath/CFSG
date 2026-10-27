module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
import Certificates.Kernel.Co1ThreeK.GlueE

public section

namespace Certificates

open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate17332 :     ∀ t ∈ Subgroup.closure {x | x ∈ Co1T.aGA}, t ≠ 1 → ∃ g : ↥GA,
      g * t * g⁻¹ = Co1T.root 0 ∨ g * t * g⁻¹ = Co1T.root 1 ∨
        g * t * g⁻¹ = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 1, 1] :=
  fun t ht h1 => CertificateChecks.KernelCo1ThreeK.classes_E
    (by rwa [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.SplitData.T_eq_closure]) h1

end Certificates
