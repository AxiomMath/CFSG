module

public import CFSG.Sporadic.ONOddCore.LiftCountInputs
import Certificates.Kernel.Sporadic.OddCore.ON2121T

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore in
theorem certificate2121 : (List.range 12).map (fun k => (liftIdxs (liftData.cands.getD k [])).length) =
      [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0] ∧
    (List.range 12).all (fun k => (liftIdxs (liftData.cands.getD k [])).Nodup) = true := KernelSpor.ON2121.facts2121_proved

end Certificates
