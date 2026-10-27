
module

public import Certificates.Certificate2309Base

public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
import Certificates.Kernel.SporSch.Th.Cent

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Pointwise in
theorem certificate2309 : centFixedIdx.length = 10200 ∧ centImageIdx.length = 120 ∧ centImageRows.length = 240 ∧
    (∀ n ∈ centImageRows, n < 2 ^ 248) ∧ centOrbitPar.length = 819 ∧
    centOrbitLab.length = 819 ∧ centOrbitEdges.length = 1638 := KernelSporSch.ThCent.facts2309

end Certificates
