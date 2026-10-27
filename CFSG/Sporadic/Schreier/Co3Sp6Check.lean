module

public import CFSG.Sporadic.Schreier.Co3Outer
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import Mathlib.Data.Matrix.Block
public import CFSG.Sporadic.Schreier.Co3Sp6CheckInputs
public import Certificates.Certificate2161

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native Matrix

@[expose] def co3J6 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) := fromBlocks 0 1 (-1) 0

@[expose] def co3TransvMat (v : Co3V6) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  1 + vecMulVec v (co3J6 *ᵥ v)

theorem co3Sp6Zeros_check : ∀ a < 64,
    decide (a ∈ co3A) = decide ((Finset.univ.filter fun n : Fin 64 =>
      co3Sp6Form a (co3Vec6 n) = 0).card = 36) :=
  Certificates.certificate2161.1

theorem co3Sp6A_check :
    co3A.Nodup ∧ 0 ∈ co3A ∧ (∀ i < 6, 2 ^ i ∈ co3A) ∧ (∀ a ∈ co3A, a < 64) :=
  Certificates.certificate2161.2.1

theorem co3Sp6Sigma_check : ∀ k < 63, ∀ r < 36, (co3Sp36Arrs[k]!)[r]! < 36 ∧
    co3A.getD (co3Sp36Arrs[k]!)[r]! 0 = co3A.getD r 0 ^^^
      (if co3Sp6Form (co3A.getD r 0) (co3Vec6 (k + 1)) = 0 then co3Sp6J (k + 1) else 0) :=
  Certificates.certificate2161.2.2.1

theorem co3Sp36_check :
    rawChainOK 36 (co3Sp36Arrs.extract 0 co3Sp36GenCount) co3Sp36Arrs co3Sp36BaseArr
      (wordsArr co3Sp36GenCount co3Sp36StrongCount co3Sp36Derivations) 4 = true ∧
    rawOrbitSizes 36 co3Sp36Arrs co3Sp36BaseArr = [36, 35, 18, 8, 4, 2] ∧
    ((rawLevels 36 co3Sp36Arrs co3Sp36BaseArr)[0]!).pts.size = 36 ∧
    (∀ c < 36, 1 ≤ c → ∃ j < 63, (co3Sp36Arrs[j]!)[0]! = 0 ∧ (co3Sp36Arrs[j]!)[c]! ≠ c) :=
  Certificates.certificate2161.2.2.2

end CFSG.Sporadic.Schreier.Co3
