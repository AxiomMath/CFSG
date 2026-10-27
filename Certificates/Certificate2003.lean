module

public import CFSG.Literature.GL52PassInputs
import Certificates.Kernel.Misc.GL52.Cls

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Literature CFSG.Literature.GL52 in
theorem certificate2003 : Nat.card {g : G // orderOf g = 2} = 6975
    ∧ Nat.card {g : G // orderOf g = 2 ∧ fixCount g = 15} = 465
    ∧ Nat.card {g : G // orderOf g = 2 ∧ fixCount g = 7} = 6510
    ∧ Nat.card {g : G // orderOf g = 3} = 75392
    ∧ Nat.card {g : G // orderOf g = 3 ∧ fixCount g = 1} = 55552
    ∧ Nat.card {g : G // orderOf g = 3 ∧ fixCount g = 7} = 19840
    ∧ Nat.card (Subgroup.centralizer {glT0}) = 21504
    ∧ Nat.card (Subgroup.centralizer {glU0}) = 1536
    ∧ Nat.card (Subgroup.centralizer {glTau1}) = 180
    ∧ Nat.card (Subgroup.centralizer {glTau2}) = 504
    ∧ Nat.card {g : G // g * glTau2 = glTau2 * g ∧ g * glTauB = glTauB * g} = 9
    ∧ Nat.card (Subgroup.centralizer {glF5}) = 15
    ∧ Nat.card {g : G // (∃ r ∈ r0Elts, g * glTau2 = r * g) ∧ ∃ r ∈ r0Elts, g * glTauB = r * g} =
      72
    ∧ Nat.card {g : G // orderOf g = 5} = 666624
    ∧ Nat.card {g : G // orderOf g = 7} = 476160
    ∧ Nat.card {g : G // orderOf g = 31} = 1935360 := KernelMisc.GL52K.facts

end Certificates
