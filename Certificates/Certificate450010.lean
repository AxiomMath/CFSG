module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28X
import Certificates.Kernel.PropA.ModelFacts
import Certificates.Kernel.PropA.X28

public section

namespace Certificates

open CertificateChecks

open Equiv Subgroup CFSG.EvenSporadicStandard.M12Std.PropA in
theorem certificate450010 : ∀ b : Bool, Model (K28 b) D28 pT x28 ∧ Nat.card ↥(K28 b) = 380160 ∧
    ∀ y ∈ D28, orderOf y = 2 → Nat.card ↥(D28 ⊓ centralizer ({y} : Set (Perm (Fin 28)))) = 240 →
      ∃ a ∈ D28, a * y * a⁻¹ = x28 := by
  refine fun b => ?_
  rw [← KernelPropA.pa450010_x_eq]
  exact KernelPropA.pa450010_model b

end Certificates
