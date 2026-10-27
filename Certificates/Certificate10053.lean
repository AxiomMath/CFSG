module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public import CFSG.RankThree.PartOne.KS.PKitSimple
import Certificates.Kernel.HeLoc.Seven1Facts
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native in
theorem certificate10053 :
    caseChainOK3 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenCase1Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenLines[1]! heSevenCase1Rels
        heSevenC1Gens heSevenKeys heSevenC1Cert 1176 = true ∧
      eqA 8330 heSevenC1Gens[0]! heSevenLines[1]! = true ∧
      derivedOKQ 7 168 8330 heSevenC1Gens heSevenDGens1 heSevenKeys heSevenC1Cert heSevenDCert1
        heSevenDWit1[0]! heSevenDWit1[1]! heSevenLines[1]! heLevels heBase.toArray = true := KernelHeLoc.Seven.facts1

end Certificates
