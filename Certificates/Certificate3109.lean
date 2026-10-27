
module

public import Certificates.Certificate3109Base
import all Certificates.Certificate3109Base

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint.NativeSporadic in
theorem certificate3109 : decode 2 4370 1 BSeed1 * decode 2 4370 1 BSeed1 = 1
    ∧ decode 2 4370 1 BSeed2 * decode 2 4370 1 BSeed2 * decode 2 4370 1 BSeed2 = 1 :=
  ⟨KernelBM.genA₁_mul_self, KernelBM.genA₂_cube⟩

end Certificates
