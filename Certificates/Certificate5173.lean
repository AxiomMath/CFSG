module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCTitsInputs
import Certificates.Kernel.TitsW.Alg
import Certificates.Kernel.TitsW.C5173
import CFSG.Certificates.Kernel.Spor.Co2ChainSound

public section

open CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelTitsW CertificateChecks.KernelTitsW.C5173 in
open CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits in
theorem certificate5173 : lettersOK 13 (titsUWord ++ yWord) = true ∧
    lettersOK 13 (xWord ++ yWord ++ titsUWord) = true ∧
    eqA 1755 (wordArr 1755 titsDerivedArrs (titsUWord ++ yWord))
      (wordArr 1755 titsDerivedArrs (xWord ++ yWord ++ titsUWord)) = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← CFSG.KS.Co2SShape.lettersK_eq]
    exact c5173_l1
  · rw [← CFSG.KS.Co2SShape.lettersK_eq]
    exact c5173_l2
  · rw [wordArr_D c5173_l1, wordArr_D c5173_l2, eqA_G (Gd_WD _) (Gd_WD _)]
    exact c5173_eq

end Certificates
