module

public import CFSG.Sporadic.SuzOddCore.OuterCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public meta import CFSG.Sporadic.SuzOddCore.CertChainCheck
import Certificates.Kernel.Sporadic.OddCore.Suz2304

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2304 : eqA 22880 (compA 22880 outerArr outerArr) (idA 22880) = true ∧
    eqA 22880 outerArr (idA 22880) = false ∧
    lettersOK 10 uRejectWord = true ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[0]! = 0 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[1]! = 1 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[2]! = 2 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[3]! = 2862 ∧
    (certStrongArrs[9]!)[(certStrongArrs[9]!)[3]!]! = 3 ∧ (certStrongArrs[9]!)[3]! ≠ 2862 ∧
    (∀ i < 2, lettersOK 10 (uStripWord i) = true ∧
      eqA 22880 (compA 22880 outerArr (compA 22880 (certArr i) outerArr))
        (wordA 22880 certStrongArrs certStrongInvs (uStripWord i)) = true) ∧
    (∀ x < 22880, x ≠ 0 → ∃ j ∈ certStabIdx, (certStrongArrs[j]!)[x]! ≠ x) := KernelSpor.OddCore.facts2304

end Certificates
