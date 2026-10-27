module

public import Certificates.Data.TabMSevenHeE8
import Certificates.Kernel.HeE8.Check
import Certificates.Kernel.LocalComp.HeFixBind
import CFSG.Certificates.Kernel.HeE8KSound

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabMSeven CFSG.Sporadic.HeldB

theorem certificate17486 : CFSG.HardMathSupport.Dickson.I271.TabMSeven.heE8Check () = true := by
  change heE8OK (heGen 0) (heGen 1) = true
  rw [KernelLC.HeFix.heGen_eq (k := 0) (by decide), KernelLC.HeFix.heGen_eq (k := 1) (by decide),
    CFSG.KC.HeE8K.heE8OK_eq, CFSG.KC.HeE8K.evPt_unpack]
  exact KernelHeE8.k17486

end Certificates
