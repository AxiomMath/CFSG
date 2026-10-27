module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import Certificates.Kernel.HeLoc.SevenQFacts
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.HeldB.HeBlocks

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB in
theorem certificate10055 :
    linesOKG 7 343 57 8330 heSevenQGens heSevenKeys heSevenQCert heSevenLines = true ∧
      allLt heSevenQGens.size (fun l => siftA 8330 heLevels heBase.toArray 0 heSevenQGens[l]!) =
        true ∧
      transOKG 57 8330 heSevenTransporters heSevenLines heSevenRec heSevenRLevels
        heSevenCase0BaseArr = true ∧
      allLt 57 (fun j => (List.range 3).any fun i => heSevenRec.getD j 0 == i) = true ∧
      heSevenRec.getD 0 0 = 0 ∧
      heSevenRec.getD 1 0 = 1 ∧
      heSevenRec.getD 2 0 = 2 := KernelHeLoc.Seven.facts

end Certificates
