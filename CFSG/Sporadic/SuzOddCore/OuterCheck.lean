module

public import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public import CFSG.Sporadic.SuzOddCore.CertChainCheck
public meta import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public meta import CFSG.Sporadic.SuzOddCore.CertChainCheck
public import CFSG.Sporadic.SuzOddCore.OuterCheckInputs
public import Certificates.Certificate2304

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem outer_check :
    eqA 22880 (compA 22880 outerArr outerArr) (idA 22880) = true ∧
    eqA 22880 outerArr (idA 22880) = false ∧
    lettersOK 10 uRejectWord = true ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[0]! = 0 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[1]! = 1 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[2]! = 2 ∧
    (compA 22880 (wordA 22880 certStrongArrs certStrongInvs uRejectWord) outerArr)[3]! = 2862 ∧
    certStrongArrs[9]![certStrongArrs[9]![3]!]! = 3 ∧ certStrongArrs[9]![3]! ≠ 2862 ∧
    (∀ i < 2, lettersOK 10 (uStripWord i) = true ∧
      eqA 22880 (compA 22880 outerArr (compA 22880 (certArr i) outerArr))
        (wordA 22880 certStrongArrs certStrongInvs (uStripWord i)) = true) ∧
    (∀ x < 22880, x ≠ 0 → ∃ j ∈ certStabIdx, certStrongArrs[j]![x]! ≠ x) :=
  Certificates.certificate2304

end CFSG.Sporadic.SuzOddCore
