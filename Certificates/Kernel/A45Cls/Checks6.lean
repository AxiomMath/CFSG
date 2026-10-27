module

public import Certificates.Kernel.A45Cls.Data3

public section

namespace CertificateChecks.KernelA45

theorem witBounds : (∀ p ∈ t0I, p < 64) ∧ t0I.length = 64 ∧ (∀ j < 3, y2p j < 64) ∧
    (∀ j < 3, ∀ l ∈ aWit j, ∀ ws ∈ l, ∀ p ∈ ws, p < 128) ∧
    (∀ j < 3, ∀ l ∈ bWit j, l.getD 0 0 < 64 ∧ l.getD 1 0 < 16) := by
  decide +kernel

end CertificateChecks.KernelA45

end
