module

public import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
import Certificates.Kernel.Sporadic.OddCore.Suz2296

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2296 : (∀ i < 4, (invText i).length = 5346 * invRunCount i + 1) ∧
    (∀ i < 4, ∀ k < invRunCount i, permOK 1782 (invRun i k) = true) ∧
    invFusionText.length = 5346 * 53 + 1 ∧ (∀ k < 53, permOK 1782 (invFusionRun k) = true) ∧
    (∀ i < 4, derivsOK (invFullGenCounts.getD i 0) (invFullDerivs i) = true ∧
      derivsOK (invInnerGenCounts.getD i 0) (invInnerDerivs i) = true ∧
      (invFullDerivs i).size = invFullStrongCounts.getD i 0 ∧
      (invInnerDerivs i).size = invInnerStrongCounts.getD i 0) ∧
    invNeighbors.length = 416 ∧ strictIncr invNeighbors = true ∧
    (∀ x ∈ invNeighbors, 0 < x ∧ x < 1782) := KernelSpor.OddCore.facts2296

end Certificates
