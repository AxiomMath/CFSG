module

public import CFSG.Quasithin.Background.Harris.R1.D4VertCheck
import Certificates.Kernel.Direct.C300205
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.Background.Harris.R1.D4Vert in
theorem certificate300205 : (gensInvolOK () = true) ∧ (relsHold hWords hRels = true) ∧
    (relsHold nWords nRels = true) :=
  ⟨KernelDirect.C300205.gensInvolOK_eq_true, KernelDirect.C300205.relsHold_h,
    KernelDirect.C300205.relsHold_n⟩

end Certificates
