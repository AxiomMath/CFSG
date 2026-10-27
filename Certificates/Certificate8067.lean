module

public import CFSG.Quasithin.Background.Sp4InfA6BasicInputs
public import CFSG.Quasithin.Background.Sp4InfA6GenInputs
import Certificates.Kernel.Misc.Perm.Sp4Reach

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf Equiv in
open scoped Pointwise in
theorem certificate8067 : (gu ∈ q1)
    ∧ (gv ∈ q2)
    ∧ ((Finset.univ.filter (fun x : Perm (Fin 6) => Perm.sign x = 1)) ⊆ reach gu gv 14) :=
  ⟨KernelMisc.Sp4Reach.gu_mem, KernelMisc.Sp4Reach.gv_mem, KernelMisc.Sp4Reach.alt_subset_reach⟩

end Certificates
