module

public import Certificates.Data.J3Cover3
import Certificates.Kernel.Cover3.J3Facts

public section

open CFSG.SectionRank.QTK.Insp443.J3Cover
open CFSG.Monster.B.Co2.Native (eqA compA idA invCand)
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (powN commN)

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.QTK.Insp443.J3Cover in
open CFSG.Monster.B.Co2.Native (eqA compA idA invCand) in
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (powN commN) in
theorem certificate589303 : j3CovSift (j3CovArr 0) = true ∧ j3CovSift (j3CovArr 1) = true ∧
    j3CovSift (j3CovArr 2) = true ∧ j3CovSift (j3CovArr 3) = true ∧
    j3CovSift (j3CovArr 4) = true ∧ j3CovSift (j3CovArr 5) = true ∧
    eqA 6156 (compA 6156 (j3CovArr 0) (j3CovArr 0)) (CFSG.Monster.B.Co2.Native.idA 6156) = true ∧
    eqA 6156 (compA 6156 (j3CovArr 1) (j3CovArr 1)) (CFSG.Monster.B.Co2.Native.idA 6156) = true ∧
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.commN 6156 (j3CovArr 0) (j3CovArr 1) = true ∧
    eqA 6156 (j3CovArr 0) (CFSG.Monster.B.Co2.Native.idA 6156) = false ∧
    eqA 6156 (CFSG.RankThree.PartTwo.Sec4.Item434SporGen.powN 6156 (j3CovArr 2) 3) (CFSG.Monster.B.Co2.Native.idA 6156) = true ∧
    eqA 6156 (CFSG.RankThree.PartTwo.Sec4.Item434SporGen.powN 6156 (j3CovArr 3) 3) (CFSG.Monster.B.Co2.Native.idA 6156) = true ∧
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.commN 6156 (j3CovArr 2) (j3CovArr 3) = true ∧
    j3CovDistinct = true ∧
    j3CovInQ (j3CovArr 2) (j3CovArr 0) = true ∧ j3CovInQ (j3CovArr 2) (j3CovArr 1) = true ∧
    j3CovInQ (j3CovArr 3) (j3CovArr 0) = true ∧ j3CovInQ (j3CovArr 3) (j3CovArr 1) = true ∧
    eqA 6156 (j3CovConj (j3CovArr 4) (j3CovArr 2)) (invCand 6156 (j3CovArr 2)) = true ∧
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.commN 6156 (j3CovArr 5) (j3CovArr 2) = true ∧
    eqA 6156 (j3CovConj (j3CovArr 5) (j3CovArr 3)) (invCand 6156 (j3CovArr 3)) = true := KernelCover3.facts589303

end Certificates

end

end
