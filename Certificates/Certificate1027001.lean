module

public import CFSG.LocalAnalysis.EvenSmallLie.Sp6RootClassInputs
public meta import CFSG.LocalAnalysis.EvenSmallLie.Sp6RootClassInputs
import Certificates.Kernel.LocalComp.Sp6Root.Facts
import Certificates.Kernel.LocalComp.Sp6Root.Checks
import Certificates.Kernel.LocalComp.Sp6J.ClsC
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.Sp6 in
theorem certificate1027001 : sp6SylowCheck () = true ∧ sp6K1Count () ≤ 7 ∧ sp6K2Check () = true := KernelLC.Sp6Root.facts

end Certificates
