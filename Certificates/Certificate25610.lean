module

public import CFSG.Sporadic.SuzOddCore.InvPerms
import Certificates.Kernel.Sporadic.Suz.Cent25610Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SuzOddCore in
theorem certificate25610 : (∀ i < 2, ∀ z ∈ suzM, z * z = 1 → z * suzInv i = suzInv i * z →
      (∀ y ∈ suzM, y * suzInv i = suzInv i * y → z * y = y * z) → z = 1 ∨ z = suzInv i) ∧
    (∀ i < 2, ∀ j < 4,
      ∃ x ∈ suzM, (x * suzInv i * x⁻¹) * suzInv j = suzInv j * (x * suzInv i * x⁻¹)) :=
  ⟨KernelSpor.SuzCI.centerInv_rep, KernelSpor.SuzCI.exists_commuting_rep⟩

end Certificates
