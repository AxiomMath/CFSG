module

public import Certificates.Data.Kernel.CentGenK
public import Certificates.Kernel.He2111.Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCentGenK.He
  "Certificates/Kernel/CentGenK/data/he.json.gz" 72429 18335328106201060883
  (prog1 : List Nat) (prog2 : List Nat) (hints : List Nat)

namespace CertificateChecks.KernelCentGenK.He

open CFSG.KC.CentGenK

@[expose] noncomputable def D : CGK where
  p := 7
  nx1 := 9
  prog1 := prog1
  is1 := 2
  is2 := 8
  ke := 3
  kf := 3
  nx2 := 13
  prog2 := prog2
  ra := 2
  rb := 10
  hints := hints

set_option maxRecDepth 400000 in
theorem he_ok : cgK 8330 14 (CFSG.KD.He2111.GnT.F 0) (CFSG.KD.He2111.GnT.F 1) D = true := by
  quickRfl

end CertificateChecks.KernelCentGenK.He
