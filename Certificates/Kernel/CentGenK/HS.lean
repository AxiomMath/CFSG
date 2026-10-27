module

public import Certificates.Data.Kernel.CentGenK
public import Certificates.Kernel.HS100.ChainData
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCentGenK.HS
  "Certificates/Kernel/CentGenK/data/hs.json.gz" 1750 15719852030503072024
  (prog1 : List Nat) (prog2 : List Nat)

namespace CertificateChecks.KernelCentGenK.HS

open CFSG.KC.CentGenK

@[expose] noncomputable def D : CGK where
  p := 5
  nx1 := 7
  prog1 := prog1
  is1 := 2
  is2 := 6
  ke := 4
  kf := 3
  nx2 := 9
  prog2 := prog2
  ra := 2
  rb := 8
  hints := []

set_option maxRecDepth 400000 in
theorem hs_ok : cgK 100 7 (CertificateChecks.KernelHS100.HP.F 0)
    (CertificateChecks.KernelHS100.HP.F 1) D = true := by
  quickRfl

end CertificateChecks.KernelCentGenK.HS
