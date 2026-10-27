module

public import CFSG.RankThree.PartOne.KE.TitsFiveCheckInputs
import Certificates.Kernel.SporSch.Tits.Five10050

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne.KE CFSG.Sporadic.Schreier.Tits in
theorem certificate10050 :
    lettersOK 13 titsFiveWord = true ∧ inH titsFiveArr = true ∧
      eqA 1755 titsFiveArr (idA 1755) = false ∧
      eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 titsFiveArr titsFiveArr)
        titsFiveArr) titsFiveArr) titsFiveArr) (idA 1755) = true ∧
      all5 1755 titsHLevels (fun a => !commA a titsFiveArr || anyEq titsCH5 a) = true ∧
      titsCH5.length = 10 ∧
      titsCH5.all (fun c => isInvA 1755 c (invCand 1755 c) && commA c titsFiveArr && inH c) = true ∧
      titsCH5.Pairwise (fun a b => eqA 1755 a b = false) := KernelSporSch.TitsFive.facts

end Certificates
