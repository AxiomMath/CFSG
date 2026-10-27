module

public import Certificates.Data.Kernel.CentGenHK
public import Certificates.Kernel.Sporadic.Tits.ChainD
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCentGenK.Tits
  "Certificates/Kernel/CentGenK/data/tits.json.gz" 462 15187653060898108032
  (prog1 : List Nat)

namespace CertificateChecks.KernelCentGenK.Tits

open CFSG.KC.CentGenK

@[expose] noncomputable def D : HPK where
  p := 3
  prog := prog1
  ke := 4
  kf := 2

set_option maxRecDepth 400000 in
theorem tits_ok : hpK 1755 11 (CertificateChecks.KernelSpor.TitsD.S 0)
    (CertificateChecks.KernelSpor.TitsD.S 1) D = true := by
  quickRfl

end CertificateChecks.KernelCentGenK.Tits
