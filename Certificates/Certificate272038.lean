module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.FusionWords
import Certificates.Kernel.J3Fusion.Fact

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition in
theorem certificate272038 :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 3 => ev (fusGl.getD j []))) = 2 ^ 7 ∧
    ∀ t ∈ Subgroup.closure (Set.range fun j : Fin 3 => ev (fusGl.getD j [])),
      t * t = 1 → t ≠ 1 → ∃ k : J3Model, k * uJ 3 * k⁻¹ = t := KernelJ3Fusion.sylowFacts

end Certificates
