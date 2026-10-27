module

public import CFSG.Monster.Tri.LeechModelFixInputs
import Certificates.Kernel.MonsterExist.ELevel.FixCount

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.Tri.Leech in
theorem certificate10049 :
    ∀ i ∈ ({1, 2, 6} : Finset ℕ), fixCountX i ≤ 4071 :=
  MonsterExist.ELevel.fixCountX_le_all

end Certificates
