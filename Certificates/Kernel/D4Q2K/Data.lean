module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelD4Q2K.D "Certificates/Kernel/D4Q2K/data/d4q2.json.gz"
  4453378 4905375780105732520 (pts : List Nat) (frames : Array (Array Nat))
#kc_repo #kc_json_family_gz CertificateChecks.KernelD4Q2K.D
  "Certificates/Kernel/D4Q2K/data/d4q2.json.gz" 4453378 4905375780105732520
  (masks : Nat) (rows : Nat)
#kc_select CertificateChecks.KernelD4Q2K.D MF masks 4480
#kc_select CertificateChecks.KernelD4Q2K.D RF rows 2240

end
