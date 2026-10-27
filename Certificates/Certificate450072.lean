module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28X
import Certificates.Kernel.PropA.NFacts
import Certificates.Kernel.PropA.X28

public section

namespace Certificates

open CertificateChecks

open Equiv Subgroup CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA in
theorem certificate450072 : ∀ b : Bool, ∀ N : Subgroup (Perm (Fin 28)),
    N ≤ K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28))) →
      (N.subgroupOf (K28 b ⊓ centralizer ({x28} : Set (Perm (Fin 28))))).Normal →
        jOf D28 x28 ≤ N → x28 ∉ N → Nat.card ↥N ≤ 120 := by
  refine fun b => ?_
  rw [← KernelPropA.pa450010_x_eq]
  exact KernelPropA.pa450010_normal_small b

end Certificates
