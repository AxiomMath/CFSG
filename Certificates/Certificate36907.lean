module

public import Certificates.Data.SuzPump
public meta import Certificates.Data.SuzPump
import Certificates.Kernel.SuzPump.PumpFuseFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump in
theorem certificate36907 : fuseCheck () = true ∧ pairCheck () = true ∧ yCheck () = true :=
  ⟨KernelSuzPump.fuse_ok, KernelSuzPump.pump_pair, KernelSuzPump.pump_y⟩

end Certificates
