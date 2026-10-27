module

public import CFSG.Sporadic.Co2Schreier.ThreeCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ThreeCheckInputs
import Certificates.Kernel.SporSch.Co2M.P0Facts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu in
theorem certificate719101 : enumOK p0Arrs 81 enumP0 = true
    ∧ p0MarkedIdx = [0, 1, 3, 20, 22, 28, 30, 32, 34, 35, 39, 41, 43, 45, 46, 49, 50, 54, 56, 57,
        60, 61, 64, 68, 69, 72, 76]
    ∧ eqA 2300 (compA 2300 enumP0.elems[4]! (compA 2300 enumP0.elems[4]! enumP0.elems[4]!))
        (idA 2300) = false
    ∧ (p0SixOK 56 [1, 55, 49, 61, 63, 32] = true ∧ p0SixOK 1 [43, 34, 5, 14, 54, 45] = true ∧
        p0SixOK 20 [1, 57, 30, 20, 2, 7] = true)
    ∧ qCentIdx56 = [0, 23] := KernelSporSch.Co2M.facts719101

end Certificates
