
module


public import CFSG.Monster.B.Fischer.Fi22OuterArrays
import Certificates.Kernel.Sporadic.Fi22.F1Model
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Certificates.Native in
theorem certificate3154 : eqA 3510 fi22GraphOuterArr (idA 3510) = false ∧
      eqA 3510 (compA 3510 fi22GraphOuterArr fi22GraphOuterArr) (idA 3510) = true ∧
      siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 fi22GraphOuterArr =
        false ∧
      (∀ k < 2, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (compA 3510 fi22GraphOuterArr (compA 3510 fi22OrigArrs[k]! fi22GraphOuterArr)) = true) ∧
      (∀ p < 3510, p ≠ 0 → ∃ k < 3, ((fi22OuterStrong3510 3)[k]!)[p]! ≠ p) := KernelSpor.Fi22F1M.facts3154

end Certificates
