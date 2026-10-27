module

public import Certificates.Data.Kernel.CentGenRK
public import Certificates.Kernel.Sporadic.Suz.Text2306
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCentGenK.Suz
  "Certificates/Kernel/CentGenK/data/suz.json.gz" 5461 9027704143372283617
  (prog1 : List Nat) (prog2 : List Nat)

namespace CertificateChecks.KernelCentGenK.Suz

open CFSG.KC.CentGenK

@[expose] noncomputable def D : CGRK where
  p := 5
  nx1 := 26
  prog1 := prog1
  ie := 24
  jf := 25
  is1 := 26
  is2 := 27
  nx2 := 19
  prog2 := prog2
  ra := 19
  rb := 20
  hints := []

set_option maxRecDepth 400000 in
theorem suz_ok : cgRK 1782 11 CertificateChecks.KernelSpor.Suz2306.B0
    CertificateChecks.KernelSpor.Suz2306.B1 D = true := by
  quickRfl

end CertificateChecks.KernelCentGenK.Suz
