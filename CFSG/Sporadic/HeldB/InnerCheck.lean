
module

public import CFSG.Sporadic.HeldB.InnerCheckBase
import all CFSG.Sporadic.HeldB.InnerCheckBase

public import CFSG.Sporadic.HeldB.InnerData
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public import Certificates.Certificate2114

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

theorem heInner_big :
    lettersOK 2 heT1Word = true ∧ permChk 8330 heT1Arr = true ∧
    eqA 8330 (compA 8330 heT1Arr heT1Arr) (idA 8330) = true ∧
    eqA 8330 heT1Arr (idA 8330) = false ∧
    eqA 8330 (compA 8330 (heGen 0) (heGen 0)) (idA 8330) = true ∧
    eqA 8330 (heGen 0) (idA 8330) = false ∧
    heInnerWords0.length = 9 ∧ heInnerWords1.length = 9 ∧
    (∀ j < 9, lettersOK 3 (heInnerWords0.getD j []) = true ∧ permChk 8330 (heInnerC0 j) = true ∧
      eqA 8330 (compA 8330 (heInnerC0 j) (heGen 0)) (compA 8330 (heGen 0) (heInnerC0 j)) = true ∧
      permChk 240 (heInnerSigma0.getD j #[]) = true ∧
      agreeOK 240 (heInnerC0 j) heDelta0 (heInnerSigma0.getD j #[]) = true) ∧
    (∀ j < 9, lettersOK 3 (heInnerWords1.getD j []) = true ∧ permChk 8330 (heInnerC1 j) = true ∧
      eqA 8330 (compA 8330 (heInnerC1 j) heT1Arr) (compA 8330 heT1Arr (heInnerC1 j)) = true ∧
      permChk 42 (heInnerSigma1.getD j #[]) = true ∧
      agreeOK 42 (heInnerC1 j) heDelta1 (heInnerSigma1.getD j #[]) = true) ∧
    incListOK 8330 240 heDelta0 = true ∧ fixesOK 240 (heGen 0) heDelta0 = true ∧
    incListOK 8330 42 heDelta1 = true ∧ fixesOK 42 heT1Arr heDelta1 = true ∧
    eqA 8330 (heInnerC0 0) (heGen 0) = true ∧ eqA 8330 (heInnerC1 0) heT1Arr = true :=
  Certificates.certificate2114.1

theorem heInner_X0 : heX0.check = true ∧ heX0.orderCertificate = 80640 ∧
    oddWitnessOK 240 315 (allTables heX0) = true :=
  Certificates.certificate2114.2.1

theorem heInner_X1 : heX1.check = true ∧ heX1.orderCertificate = 10752 ∧
    oddWitnessOK 42 21 (allTables heX1) = true :=
  Certificates.certificate2114.2.2

end CFSG.Sporadic.HeldB
