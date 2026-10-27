module

public import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.McL.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation in
open CFSG.CosetTable in
theorem certificate9124 : Finite TauCeti.SporadicName.McL.Group := KernelMcL.mcl.1

end Certificates
