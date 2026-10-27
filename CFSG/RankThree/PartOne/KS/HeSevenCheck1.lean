module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public meta import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public import CFSG.RankThree.PartOne.KS.PKitSimple
public import Certificates.Certificate10053
public meta import CFSG.RankThree.PartOne.KS.PKitSimple
public meta import CFSG.RankThree.PartOne.KS.HeSevenData
public meta import CFSG.RankThree.PartOne.KS.HeSevenAux
public meta import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.PartOne.KS.PKitLines
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.RankThree.Native.FiveKit
public meta import CFSG.RankThree.Native.DerivedGenerators
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.Monster.B.Fischer.ArrCert
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.RankThree.PartOne.KS.PKitLines
public meta import Mathlib
public import Mathlib

public noncomputable section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Sporadic.HeldB

theorem heSeven_case1_check :
    caseChainOK3 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenCase1Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenLines[1]! heSevenCase1Rels
        heSevenC1Gens heSevenKeys heSevenC1Cert 1176 = true ∧
      eqA 8330 heSevenC1Gens[0]! heSevenLines[1]! = true ∧
      derivedOKQ 7 168 8330 heSevenC1Gens heSevenDGens1 heSevenKeys heSevenC1Cert heSevenDCert1
        heSevenDWit1[0]! heSevenDWit1[1]! heSevenLines[1]! heLevels heBase.toArray = true :=
  Certificates.certificate10053

end CFSG.RankThree.PartOne
