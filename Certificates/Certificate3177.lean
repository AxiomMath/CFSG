module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23UnitaryInputs
public import CFSG.Monster.B.TwoA.Unitary.Form
import Certificates.Kernel.TwoE6.Unitary
import Certificates.Data.Kernel.S23Unitary
import Certificates.Kernel.TwoE6.UnitaryData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.TwoA.Unitary CFSG.Fischer in
theorem certificate3177 : (rowsGeom (wordRows nuWord) 11 = zeroRows)
    ∧ (nuPowM 0 = 1)
    ∧ (nuPowM 1 = nuMat)
    ∧ (∀ i < 5, nuPowM (i + 1) = nuPowM i * nuPowM 1)
    ∧ (nuPowM 5 * nuPowM 5 * nuPowM 1 = 1)
    ∧ (Matrix.trace (nuPowM 1) ≠ Matrix.trace (barM (nuPowM 1)))
    ∧ (cycInv * cycMat = 1)
    ∧ (∀ c : Fin 6 → F4,
       IsScalarM ((∑ i : Fin 6, c i • nuPowM i) * ∑ i : Fin 6, c i • nuPowM i) →
         IsScalarM (∑ i : Fin 6, c i • nuPowM i)) := KernelTwoE6.cert3177

end Certificates
