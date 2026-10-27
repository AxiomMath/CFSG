module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import Certificates.Kernel.HeLoc.Seven2Facts
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native in
theorem certificate10054 :
    caseChainOK3 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenCase2Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenLines[2]! heSevenCase2Rels
        heSevenC2Gens heSevenKeys heSevenC2Cert 98 = true ∧
      eqA 8330 heSevenC2Gens[0]! heSevenLines[2]! = true ∧
      normalOKP 7 8330 heSevenC2Gens heSevenA2Gens heSevenKeys heSevenC2Cert heSevenA2Cert 49
        heLevels heBase.toArray = true ∧
      selfCentOKG 8330 heSevenA2Gens heSevenC2Cert heSevenA2Cert = true := KernelHeLoc.Seven.facts2

end Certificates
