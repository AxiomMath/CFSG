module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28X
import Certificates.Kernel.PropA.YFacts
import Certificates.Kernel.PropA.X28

public section

namespace Certificates

open CertificateChecks

open Equiv Subgroup CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA in
theorem certificate450070 : ∀ b : Bool,
    (∀ a ∈ centralizer (jOf D28 x28 : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28)))),
      ∀ c ∈ centralizer (jOf D28 x28 : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28)))), a * c = c * a) ∧
    (∀ y ∈ centralizer (jOf D28 x28 : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28)))), y ^ 4 = 1) ∧
    centralizer (jOf D28 x28 : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28)))) ⊓ D28 = zpowers x28 ∧
    K28 b ⊓ normalizer (jOf D28 x28 : Set (Perm (Fin 28))) =
      K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28))) ∧
    ((∀ y ∈ centralizer (jOf D28 x28 : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28)))), y * y = 1) →
      centralizer ((K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28))) :
          Subgroup (Perm (Fin 28))) : Set (Perm (Fin 28))) ⊓
          (centralizer (jOf D28 x28 : Set (Perm (Fin 28))) ⊓
            (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28))))) =
        closure ({pT, x28} : Set (Perm (Fin 28))) ∧
      ∃ o ∈ centralizer (jOf D28 x28 : Set (Perm (Fin 28))) ⊓
          (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28)))),
        ∃ n ∈ K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28))), n * o * n⁻¹ = o * x28) := by
  refine fun b => ?_
  rw [← KernelPropA.pa450010_x_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := KernelPropA.pa450010_rbcY b
  exact ⟨h1, h2, h3, h4, fun _ => ⟨h5, h6⟩⟩

end Certificates
