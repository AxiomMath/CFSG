module

import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json_gz_eval CertificateChecks.KernelAsch54.Co2D
  "Certificates/Kernel/Asch54/data/co2sgs.json.gz" 130235 621413881869151543
  (sA : Array (Array Nat)) (bA : Array Nat) (sB : Array (Array Nat)) (bB : Array Nat)
  (wA : List (List Nat)) (wB : List (List Nat))

namespace CertificateChecks.KernelAsch54.Co2D

@[expose] public def dNil : List (List Int) := []

end CertificateChecks.KernelAsch54.Co2D
