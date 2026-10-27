module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import Certificates.Kernel.HeLoc.Seven0Facts
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native in
theorem certificate10052 :
    caseChainOK3 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenCase0Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenLines[0]! heSevenCase0Rels
        heSevenC0Gens heSevenKeys heSevenC0Cert 2058 = true ∧
      eqA 8330 heSevenC0Gens[0]! heSevenLines[0]! = true ∧
      normalOKP 7 8330 heSevenC0Gens heSevenA0Gens heSevenKeys heSevenC0Cert heSevenA0Cert 343
        heLevels heBase.toArray = true ∧
      zCentOKP 7 8330 heSevenA0Gens heSevenC0Cert heSevenA0Cert heSevenLines[0]! = true := KernelHeLoc.Seven.facts0

end Certificates
