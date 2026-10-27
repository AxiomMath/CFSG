module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public import Certificates.Certificate10052
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

theorem heSeven_case0_check :
    caseChainOK3 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenCase0Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenLines[0]! heSevenCase0Rels
        heSevenC0Gens heSevenKeys heSevenC0Cert 2058 = true ∧
      eqA 8330 heSevenC0Gens[0]! heSevenLines[0]! = true ∧
      normalOKP 7 8330 heSevenC0Gens heSevenA0Gens heSevenKeys heSevenC0Cert heSevenA0Cert 343
        heLevels heBase.toArray = true ∧
      zCentOKP 7 8330 heSevenA0Gens heSevenC0Cert heSevenA0Cert heSevenLines[0]! = true :=
  Certificates.certificate10052

end CFSG.RankThree.PartOne
