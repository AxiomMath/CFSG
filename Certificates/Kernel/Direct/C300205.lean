module

public import CFSG.Quasithin.Background.Harris.R1.D4VertCheck
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords

public section

namespace CertificateChecks.KernelDirect.C300205

open CFSG.Quasithin.Background.Harris.R1.D4Vert

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem gensInvolOK_eq_true : gensInvolOK () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem relsHold_h : relsHold hWords hRels = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem relsHold_n : relsHold nWords nRels = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C300205
