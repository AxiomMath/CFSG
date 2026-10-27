module

public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentAux
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import Certificates.Kernel.SporSch.HeT.W2117
import Certificates.Kernel.SporSch.HeT.C2117
import Certificates.Certificate2112

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier in
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native in
open CFSG.Sporadic.Th.Native in
theorem certificate2117 : (lettersOK 3 heCentW1 = true ∧ lettersOK 3 heCentW2 = true ∧
      (∀ j < 3, lettersOK 2 (heDerivedV.getD j []) = true) ∧ permChk 8330 heUArr = true ∧
      (∀ j < 2, permChk 8330 heCArrs[j]! = true) ∧
      (∀ j < 2, eqA 8330 (compA 8330 heCArrs[j]! heUArr) (compA 8330 heUArr heCArrs[j]!) = true) ∧
      (∀ j < 2, siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0
        heCArrs[j]! = true) ∧
      fixListOK 8330 98 heUArr heFixU = true ∧ permChk 98 heSigma1 = true ∧
      permChk 98 heSigma2 = true ∧ agreeOK 98 heCArrs[0]! heFixU heSigma1 = true ∧
      agreeOK 98 heCArrs[1]! heFixU heSigma2 = true ∧
      (∀ j < 3, permChk 98 (heTauArr j) = true ∧
        agreeOK 98 (heDArr j) heFixU (heTauArr j) = true)
    )
    ∧ (heQC.check = true ∧ heQC.orderCertificate = 15120 ∧ heQD.check = true ∧
      heQD.orderCertificate = 7560 ∧ heQE.check = true ∧ heQE.orderCertificate = 7560 ∧
      permChk 98 (heEpsArr 0) = true ∧ permChk 98 (heEpsArr 1) = true ∧ permChk 98 heZ = true ∧
      heQD.sift (permOrId 98 heZ) 0 = true ∧
      (∀ j < 3, eqA 98 (compA 98 heZ (heTauArr j)) (compA 98 (heTauArr j) heZ) = true) ∧
      eqA 98 heZ (CFSG.Monster.B.Co2.Native.idA 98) = false ∧ eqA 98 (compA 98 heZ (compA 98 heZ heZ)) (CFSG.Monster.B.Co2.Native.idA 98) = true ∧
      (allTables heQD).countP (CFSG.Sporadic.Schreier.Native.commAll 98 (heTauGens.map toTable)) = 3 ∧
      fixListOK 98 35 heZ heFixZ = true ∧
      (∀ j < 3, permChk 35 (heUpsilon.getD j #[]) = true ∧
        agreeOK 35 (heTauArr j) heFixZ (heUpsilon.getD j #[]) = true) ∧
      heQY.check = true ∧ heQY.orderCertificate = 2520
    )
    ∧ (classOK 35 heYGens heYGensInv (allTables heQY) 3000 = true ∧
      (classes 35 heYGens heYGensInv (allTables heQY) 3000).map (fun c => c.2.1.size) =
        [630, 210, 360, 360, 504, 105, 70, 280, 1] ∧
      (classes 35 heYGens heYGensInv (allTables heQY) 3000).map
        (fun c => (allTables heQY).countP (commT 35 c.1)) = [4, 12, 7, 7, 5, 24, 36, 9, 2520]
    ) :=
  ⟨KernelSporSch.HeW17.big, KernelSporSch.HeQ17.small, KernelSporSch.HeQ17.classes_ok⟩

end Certificates
