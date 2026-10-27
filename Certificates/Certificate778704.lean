module

public import CFSG.CGT.Stroth77.NonSplit.Type100MnsInputs
import Certificates.Kernel.Direct.C778704

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelDirect.C778704 in
open CFSG.CGT.Stroth77 in
theorem certificate778704 : (∀ x y : Torus (Type100.k 1), toA (x + y) = toA x * toA y)
    ∧ (∀ x y : Torus (Type100.k 1), toA x = toA y → x = y)
    ∧ (∀ x : Torus (Type100.k 1), toA x ∈ bfsList gensA 60)
    ∧ (∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φuv x) = mnsUV⁻¹ * toA x * mnsUV)
    ∧ (∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φt x) = mnsT⁻¹ * toA x * mnsT)
    ∧ (∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φu x) = mnsU⁻¹ * toA x * mnsU)
    ∧ (∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φρ x) = mnsRho⁻¹ * toA x * mnsRho) :=
  ⟨toA_add, toA_inj, toA_mem, toA_uv, toA_t, toA_u, toA_rho⟩

end Certificates
