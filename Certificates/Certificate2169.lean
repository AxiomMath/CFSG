
module

public import Certificates.Certificate2169Base

public import CFSG.Sporadic.Schreier.J4SCommGenInputs
import Certificates.Kernel.SporSch.J4S.CommGen

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2.Native in
open MulAction in
theorem certificate2169 : ∀ c < 2048, ∃ m < 2048, xorSub (commPicks.map commVec) m = c := KernelSporSch.J4CommGen.facts

end Certificates
