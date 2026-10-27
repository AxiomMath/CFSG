module

public import Certificates.Data.Kernel.CentGenK
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCentGenK.M12
  "Certificates/Kernel/CentGenK/data/m12.json.gz" 390 13208443776049818065
  (prog1 : List Nat) (prog2 : List Nat)

namespace CertificateChecks.KernelCentGenK.M12

open CFSG.KC.CentGenK

@[expose] noncomputable def A0 : Nat := 92532767328531

@[expose] noncomputable def A1 : Nat := 180734465348391

@[expose] noncomputable def D : CGK where
  p := 3
  nx1 := 2
  prog1 := prog1
  is1 := 0
  is2 := 1
  ke := 2
  kf := 2
  nx2 := 1
  prog2 := prog2
  ra := 0
  rb := 1
  hints := []

theorem m12_ok : cgK 12 4 A0 A1 D = true := by
  quickRfl

end CertificateChecks.KernelCentGenK.M12
