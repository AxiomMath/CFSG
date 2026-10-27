module

public import CFSG.Milestones.ASVolI.F48.Small.U42eInputs
import Certificates.Kernel.F48Small.U42eGlue

public section

open CFSG CFSG.ASVolI

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7556 : burnsideF48s_u42eCheckClass () = true := KernelF48S.checkClass

end Certificates
