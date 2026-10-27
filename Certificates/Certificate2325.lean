
module

public import Certificates.Certificate2325Base

public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
import Certificates.Kernel.SporSch.Th.UA2325

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Pointwise in
theorem certificate2325 : eqRows (mulRows (mulRows rowsUAP rowsAmI) rowsUAQ) rowsD120 = true ∧
    eqRows (mulRows rowsUAPInv rowsUAP) idRows = true ∧
    eqRows (mulRows rowsUAQ rowsUAQInv) idRows = true ∧
    (∀ n ∈ uaRowsTxt, n < 2 ^ 248) ∧ uaRowsTxt.length = 4 * 248 := KernelSporSch.ThUA.facts

end Certificates
