module

import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo
meta import Certificates.Kernel.Misc.PackJson
import Certificates.Kernel.Misc.PackJson

set_option maxRecDepth 400000

#kc_repo #kc_json_gz_eval CertificateChecks.KernelCU43Aut.SylJ
  "Certificates/Kernel/CU43Aut/data/syl.json.gz" 1243842 18056499723401204445
  (tg : Array (Array Nat))

public section

#kc_repo #kmisc_json_pack CertificateChecks.KernelCU43Aut
  "Certificates/Kernel/CU43Aut/data/syl.json.gz" 1243842 18056499723401204445
  (W WP 10) (WJ WJ 0) (SW SWP 10)

end
