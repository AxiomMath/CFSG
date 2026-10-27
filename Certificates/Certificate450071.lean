module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28
import Certificates.Kernel.PropA.PFacts

public section

namespace Certificates

open CertificateChecks

open Equiv Subgroup CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA in
theorem certificate450071 : ∀ b : Bool, ∀ c ∈ K28 b, c ^ 2 ∈ zpowers pT → c ∉ zpowers pT →
    ∀ Q ≤ D28 ⊓ centralizer ({c} : Set (Perm (Fin 28))), ⁅Q, Q⁆ = Q → Q = ⊥ ∨
      ∃ x ∈ D28, orderOf x = 2 ∧ Nat.card ↥(D28 ⊓ centralizer ({x} : Set (Perm (Fin 28)))) = 240 ∧
        Q = jOf D28 x ∧ D28 ⊓ centralizer (jOf D28 x : Set (Perm (Fin 28))) = zpowers x :=
  KernelPropA.pa450010_perfect_cent

end Certificates
