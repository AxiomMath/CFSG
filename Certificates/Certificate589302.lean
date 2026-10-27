module

public import Certificates.Data.McLCover3
import Certificates.Kernel.Cover3.McLFacts

public section

open CFSG.SectionRank.QTK.Insp443.McLCover
open CFSG.Monster.B.Co2.Native (eqA compA idA invCand)
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (powN commN)

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.QTK.Insp443.McLCover in
open CFSG.Monster.B.Co2.Native (eqA compA idA invCand) in
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (powN commN) in
theorem certificate589302 : mclCovSift (mclCovArr 0) = true ∧ mclCovSift (mclCovArr 1) = true ∧
    mclCovSift (mclCovArr 2) = true ∧ mclCovSift (mclCovArr 3) = true ∧
    mclCovSift (mclCovArr 4) = true ∧
    eqA 275 (compA 275 (mclCovArr 0) (mclCovArr 0)) (idA 275) = true ∧
    eqA 275 (mclCovArr 0) (idA 275) = false ∧
    eqA 275 (CFSG.RankThree.PartTwo.Sec4.Item434SporGen.powN 275 (mclCovArr 1) 3) (idA 275) = true ∧
    eqA 275 (CFSG.RankThree.PartTwo.Sec4.Item434SporGen.powN 275 (mclCovArr 2) 3) (idA 275) = true ∧
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.commN 275 (mclCovArr 1) (mclCovArr 2) = true ∧
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.commN 275 (mclCovArr 1) (mclCovArr 0) = true ∧
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.commN 275 (mclCovArr 2) (mclCovArr 0) = true ∧
    mclCovDistinct = true ∧
    eqA 275 (mclCovConj (mclCovArr 3) (mclCovArr 1)) (invCand 275 (mclCovArr 1)) = true ∧
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.commN 275 (mclCovArr 4) (mclCovArr 1) = true ∧
    eqA 275 (mclCovConj (mclCovArr 4) (mclCovArr 2)) (invCand 275 (mclCovArr 2)) = true := KernelCover3.facts589302

end Certificates

end

end
