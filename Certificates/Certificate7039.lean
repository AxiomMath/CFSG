
module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoGLInputs
import CFSG.Certificates.Kernel.L34ModSound
import Certificates.Kernel.L34Mod.S1
import Certificates.Kernel.L34Mod.S2

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam in
theorem certificate7039 : ∀ (u : Fin 4 → Fin 16), (∀ x, lin u (lin u x) = x) →
    ∀ (v : Fin 4 → Fin 16), (∀ x, lin v (lin v (lin v x)) = x) →
    (∀ x, x ≠ 0 → lin v x ≠ x) → (∀ x, (lin u ∘ lin v)^[5] x = x) →
    ∃ w : Fin 16, (∀ x y, lin (conjMap u v w) x = lin (conjMap u v w) y → x = y) ∧
      (∀ x, lin (conjMap u v w) (lin refA x) = lin u (lin (conjMap u v w) x)) ∧
      ∀ x, lin (conjMap u v w) (lin refB x) = lin v (lin (conjMap u v w) x) :=
  CFSG.KC.L34Mod.module_unique_of_scans KernelL34Mod.s1_all KernelL34Mod.s2_all

end Certificates
