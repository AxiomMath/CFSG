module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenPFam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
import Certificates.Kernel.J4Ov.Glue4206

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.J4Ov in
open CFSG.Quasithin.J4Loc (z0) in
theorem certificate4206 : (∀ ℓ, (ℓ = 5 ∨ ℓ = 6) → ∀ h ∈ Hj, ∃ i < 49, ∃ q ∈ P0,
      q • (h • (uEl ℓ • w₀)) = (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ • w₀) ∧
    ∀ i < 49, (repData.getD i ⟨0, "", true, 0⟩).exc = true →
      zEl (repData.getD i ⟨0, "", true, 0⟩) * z0 * (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ ∈
        Eg uJ 11 :=
  ⟨fun _ hℓ _ hh => KernelJ4Ov.orbit_cover4206 hℓ hh,
    fun _ hi hexc => KernelJ4Ov.exc_cert4206 hi hexc⟩

end Certificates
