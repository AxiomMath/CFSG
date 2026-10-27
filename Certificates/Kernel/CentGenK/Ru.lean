module

public import Certificates.Data.Kernel.CentGenK
public import Certificates.Kernel.SporSch.Ru.Text4060
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCentGenK.Ru
  "Certificates/Kernel/CentGenK/data/ru.json.gz" 4299 17766983034886599123
  (prog1 : List Nat) (prog2 : List Nat)

namespace CertificateChecks.KernelCentGenK.Ru

open CFSG.KC.CentGenK

@[expose] noncomputable def D : CGK where
  p := 5
  nx1 := 6
  prog1 := prog1
  is1 := 2
  is2 := 5
  ke := 4
  kf := 3
  nx2 := 14
  prog2 := prog2
  ra := 2
  rb := 12
  hints := []

set_option maxRecDepth 400000 in
theorem ru_ok : cgK 4060 12 (CertificateChecks.KernelSporSch.RuT4060.L 0)
    (CertificateChecks.KernelSporSch.RuT4060.L 1) D = true := by
  quickRfl

end CertificateChecks.KernelCentGenK.Ru
