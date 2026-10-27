module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public import Certificates.Certificate10054
public meta import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
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

theorem heSeven_case2_check :
    caseChainOK3 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenCase2Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenLines[2]! heSevenCase2Rels
        heSevenC2Gens heSevenKeys heSevenC2Cert 98 = true ∧
      eqA 8330 heSevenC2Gens[0]! heSevenLines[2]! = true ∧
      normalOKP 7 8330 heSevenC2Gens heSevenA2Gens heSevenKeys heSevenC2Cert heSevenA2Cert 49
        heLevels heBase.toArray = true ∧
      selfCentOKG 8330 heSevenA2Gens heSevenC2Cert heSevenA2Cert = true :=
  Certificates.certificate10054

end CFSG.RankThree.PartOne
