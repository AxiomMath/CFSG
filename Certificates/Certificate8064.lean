module

public import CFSG.Quasithin.Background.G2UGroupsInputs
import Certificates.Kernel.Misc.Perm.G2U

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.G2U in
theorem certificate8064 : Nat.card rootGroup = 12096 ∧ Nat.card graphD = 6048 ∧
    (∀ g ∈ graphD, g.1 = 1 → g.2 = 1) ∧ (∀ g ∈ graphD, g.2 = 1 → g.1 = 1) := KernelMisc.G2U.facts

end Certificates
