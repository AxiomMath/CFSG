
module

public import Certificates.Kernel.Co1M.C10072T

public section

namespace CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.Odd

open Certificates in
open CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.Co1.OddCentNative in
theorem c10072 :
    ∃ T : VTree, centOK T = true := by
  refine ⟨cm72Tree, ?_⟩
  unfold centOK
  rw [cm72_comm, cm72_tree.1, cm72_tree.2]
  rfl

end CertificateChecks.KernelCo1M

end
