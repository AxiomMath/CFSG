module

public import Certificates.Data.Co2Pump

public section

namespace CertificateChecks.KernelCo2Pump

open CFSG.HardMathSupport.Solomon.Coordinator.Co2Pump

@[expose] def pumpRows : Array (Array Nat) := Array.ofFn (n := 6) fun i => pumpPerm i.val

end CertificateChecks.KernelCo2Pump

end
