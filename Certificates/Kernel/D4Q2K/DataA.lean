module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_family_gz CertificateChecks.KernelD4Q2K.DA
  "Certificates/Kernel/D4Q2K/data/d4q2a.json.gz" 6851027 4765754319159897035 (fp : Nat)
  (xc : Nat) (cx : Nat) (ap : List Nat)
#kc_select CertificateChecks.KernelD4Q2K.DA FP fp 64
#kc_select CertificateChecks.KernelD4Q2K.DA XC xc 4989
#kc_select CertificateChecks.KernelD4Q2K.DA CX cx 4989
#kc_listDispatch CertificateChecks.KernelD4Q2K.DA AP ap 4480

end
