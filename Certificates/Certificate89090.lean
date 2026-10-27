module

public import Certificates.Data.J2ThreeB
import Certificates.Kernel.Misc.Perm.J2ThreeB

public section

namespace Certificates

open CertificateChecks

theorem certificate89090 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.C89090.check89090A () = true ∧
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.C89090.check89090B () = true := KernelMisc.J2ThreeB.facts

end Certificates
