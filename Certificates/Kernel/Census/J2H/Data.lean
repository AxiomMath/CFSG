module

import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json_gz_eval CertificateChecks.KernelJ2H
  "Certificates/Kernel/Census/J2H/data/j2h.json.gz" 11597 12118969505228815595
  (s0Strong : Array (Array Nat)) (s0Base : Array Nat) (a5Strong : Array (Array Nat))
  (a5Base : Array Nat) (vStrong : Array (Array Nat)) (vBase : Array Nat)

namespace CertificateChecks.KernelJ2H

@[expose] public def noD : List (List Int) := []

end CertificateChecks.KernelJ2H
