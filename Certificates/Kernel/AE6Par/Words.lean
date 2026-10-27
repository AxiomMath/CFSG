module

public import Certificates.Data.AE6ParData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAE6Par

open Certificates.AE6Par

theorem ae6par_words : chkWords () = true := by
  decide +kernel

end CertificateChecks.KernelAE6Par
