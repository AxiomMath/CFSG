module

public import CFSG.Sporadic.Schreier.Co3Sp6CheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import Mathlib.Data.Matrix.Block
import Certificates.Kernel.Sporadic.Co3.Sp6Facts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native Matrix in
theorem certificate2161 : (∀ a < 64,
      decide (a ∈ co3A) = decide ((Finset.univ.filter fun n : Fin 64 =>
        co3Sp6Form a (co3Vec6 n) = 0).card = 36)
    )
    ∧ (co3A.Nodup ∧ 0 ∈ co3A ∧ (∀ i < 6, 2 ^ i ∈ co3A) ∧ (∀ a ∈ co3A, a < 64))
    ∧ (∀ k < 63, ∀ r < 36, (co3Sp36Arrs[k]!)[r]! < 36 ∧
      co3A.getD (co3Sp36Arrs[k]!)[r]! 0 = co3A.getD r 0 ^^^
        (if co3Sp6Form (co3A.getD r 0) (co3Vec6 (k + 1)) = 0 then co3Sp6J (k + 1) else 0)
    )
    ∧ (rawChainOK 36 (co3Sp36Arrs.extract 0 co3Sp36GenCount) co3Sp36Arrs co3Sp36BaseArr
        (wordsArr co3Sp36GenCount co3Sp36StrongCount co3Sp36Derivations) 4 = true ∧
      rawOrbitSizes 36 co3Sp36Arrs co3Sp36BaseArr = [36, 35, 18, 8, 4, 2] ∧
      ((rawLevels 36 co3Sp36Arrs co3Sp36BaseArr)[0]!).pts.size = 36 ∧
      (∀ c < 36, 1 ≤ c → ∃ j < 63, (co3Sp36Arrs[j]!)[0]! = 0 ∧ (co3Sp36Arrs[j]!)[c]! ≠ c)
    ) := KernelSpor.Co3Sp6.facts

end Certificates
