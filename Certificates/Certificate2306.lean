module

public import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.Suz.Order2306
import Certificates.Certificate9130

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2306 : rawChainOK 1782 smallGenArrs smallStrongArrs smallBaseNat.toArray smallDerivs 4 = true ∧
    rawOrbitSizes 1782 smallStrongArrs smallBaseNat.toArray = [1782, 416, 100, 63, 32, 3] ∧
    eqA 1782 (compA 1782 vArr vArr) (idA 1782) = true ∧ vArr[0]! ≠ 0 ∧
    siftA 1782 smallLevels smallBaseNat.toArray 0 vArr = false ∧
    siftA 1782 smallLevels smallBaseNat.toArray 0 (compA 1782 vArr (compA 1782 b0Arr vArr)) =
      true ∧
    siftA 1782 smallLevels smallBaseNat.toArray 0 (compA 1782 vArr (compA 1782 b1Arr vArr)) =
      true ∧
    (∀ x < 1782, x ≠ 0 → ∃ j ∈ levelIdx smallStrongArrs smallBaseNat.toArray 1,
      (smallStrongArrs[j]!)[x]! ≠ x) := KernelSpor.Suz2306.facts

end Certificates
