module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_family_gz CertificateChecks.KernelD4Q2K.DT
  "Certificates/Kernel/D4Q2K/data/d4q2t.json.gz" 8765854 3272878262049624586 (tw : List Nat)
  (tf : Nat)
#kc_listDispatch CertificateChecks.KernelD4Q2K.DT TW tw 4480
#kc_select CertificateChecks.KernelD4Q2K.DT TF tf 4480

end
