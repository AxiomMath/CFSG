
module

public import Certificates.Certificate2114Base

public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import Certificates.Kernel.SporSch.HeT.B2114
import Certificates.Kernel.SporSch.HeT.O2114

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSporSch.HeX14

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier in
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native in
open CFSG.Sporadic.Th.Native in
theorem certificate2114 : (lettersOK 2 heT1Word = true ∧ permChk 8330 heT1Arr = true ∧
      eqA 8330 (compA 8330 heT1Arr heT1Arr) (CFSG.Monster.B.Co2.Native.idA 8330) = true ∧
      eqA 8330 heT1Arr (CFSG.Monster.B.Co2.Native.idA 8330) = false ∧
      eqA 8330 (compA 8330 (heGen 0) (heGen 0)) (CFSG.Monster.B.Co2.Native.idA 8330) = true ∧
      eqA 8330 (heGen 0) (CFSG.Monster.B.Co2.Native.idA 8330) = false ∧
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
      eqA 8330 (heInnerC0 0) (heGen 0) = true ∧ eqA 8330 (heInnerC1 0) heT1Arr = true
    )
    ∧ (heX0.check = true ∧ heX0.orderCertificate = 80640 ∧
      oddWitnessOK 240 315 (allTables heX0) = true
    )
    ∧ (heX1.check = true ∧ heX1.orderCertificate = 10752 ∧
      oddWitnessOK 42 21 (allTables heX1) = true
    ) :=
  ⟨KernelSporSch.HeB14.big, ⟨x0_check.1, x0_check.2, x0_odd⟩, ⟨x1_check.1, x1_check.2, x1_odd⟩⟩

end Certificates
