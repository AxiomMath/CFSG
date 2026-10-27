module

public import CFSG.Sporadic.Fi22.Classes
import Certificates.Kernel.Fi22Fuse.Sound

public section

namespace Certificates

theorem certificate25240 : ∀ {x : CFSG.Sporadic.Fi22.J},
    orderOf x = 2 → ∃ c : CFSG.Sporadic.Fi22.J,
      c * x * c⁻¹ ∈ Subgroup.closure
        {y | y ∈ CFSG.Sporadic.Fi22.D ∧ y ∈ CFSG.Sporadic.Fi22.slvl 0} :=
  fun hx => CertificateChecks.KernelFi22Fuse.exists_conj_mem_fuseSpan hx

end Certificates
