module

public import CFSG.Milestones.ASVolI.F48.Small.U42eInputs
import Certificates.Kernel.F48Small.U42eGlue

public section

open CFSG CFSG.ASVolI

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7554 : burnsideF48s_u42eCheckClosed () = true := KernelF48S.checkClosed

end Certificates
