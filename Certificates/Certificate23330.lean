module

public import Certificates.Data.SolMaxHeGen
import Certificates.Kernel.SchreierFam.C23330G
import Certificates.Kernel.SchreierFam.C23330I

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.HeGen in
theorem certificate23330 : heGenOuterCheck = true ∧ heGenInnerCheck = true :=
  ⟨KernelSchreierFam.He23330.heGenOuter_23330, KernelSchreierFam.heGenInner_23330⟩

end Certificates
