module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelD4Q2K.DS "Certificates/Kernel/D4Q2K/data/d4q2s.json.gz"
  4513186 18223219231469782994 (sp : List (List Nat)) (si : List (List Nat))
#kc_repo #kc_json_family_gz CertificateChecks.KernelD4Q2K.DS
  "Certificates/Kernel/D4Q2K/data/d4q2s.json.gz" 4513186 18223219231469782994 (sol : Nat)
#kc_select CertificateChecks.KernelD4Q2K.DS SF sol 2240

end
