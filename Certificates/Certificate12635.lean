module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import Certificates.Kernel.Co2Chain.He12635

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier in
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native in
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert in
theorem certificate12635 : ((lettersOK 2 (heThreeWordsA.getD 0 []) = true ∧ permChk 8330 heThreeBA = true ∧
        eqA 8330 (compA 8330 heThreeBA (compA 8330 heThreeBA heThreeBA)) (idA 8330) = true ∧
        eqA 8330 heThreeBA (idA 8330) = false ∧ heThreeBA[0]! = 0 ∧
        (List.range 8330).countP (fun i => heThreeBA[i]! == i) = 77) ∧
      (heThreeWordsA.length = 4 ∧
        ∀ j < 4, lettersOK 2 (heThreeWordsA.getD j []) = true ∧ permChk 8330 (heThreeCA j) = true ∧
          eqA 8330 (compA 8330 (heThreeCA j) heThreeBA) (compA 8330 heThreeBA (heThreeCA j)) = true ∧
          permChk 35 (heThreeSigmaA.getD j #[]) = true ∧
          agreeOK 35 (heThreeCA j) heThreeDeltaA (heThreeSigmaA.getD j #[]) = true) ∧
      (incListOK 8330 35 heThreeDeltaA = true ∧ fixesOK 35 heThreeBA heThreeDeltaA = true ∧
        eqA 8330 (heThreeCA 0) heThreeBA = true))
    ∧ ((lettersOK 2 (heThreeWordsB.getD 0 []) = true ∧ permChk 8330 heThreeBB = true ∧
        eqA 8330 (compA 8330 heThreeBB (compA 8330 heThreeBB heThreeBB)) (idA 8330) = true ∧
        eqA 8330 heThreeBB (idA 8330) = false ∧ heThreeBB[0]! = 0 ∧
        (List.range 8330).countP (fun i => heThreeBB[i]! == i) = 8) ∧
      (heThreeWordsB.length = 4 ∧
        ∀ j < 4, lettersOK 2 (heThreeWordsB.getD j []) = true ∧ permChk 8330 (heThreeCB j) = true ∧
          eqA 8330 (compA 8330 (heThreeCB j) heThreeBB) (compA 8330 heThreeBB (heThreeCB j)) = true ∧
          permChk 8 (heThreeSigmaB.getD j #[]) = true ∧
          agreeOK 8 (heThreeCB j) heThreeDeltaB (heThreeSigmaB.getD j #[]) = true) ∧
      (incListOK 8330 8 heThreeDeltaB = true ∧ fixesOK 8 heThreeBB heThreeDeltaB = true ∧
        eqA 8330 (heThreeCB 0) heThreeBB = true)) :=
  CertificateChecks.KernelCo2Chain.He12635.facts

end Certificates
