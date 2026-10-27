module

public import CFSG.RankThree.PartOne.KS.RuFiveData
public import CFSG.RankThree.PartOne.KS.RuFiveAux
public import CFSG.RankThree.Native.HSMcLFiveCheck
public import CFSG.Sporadic.Schreier.RuDefs
public import CFSG.RankThree.PartOne.KS.RuFiveCheckInputs
public import Certificates.Certificate10057
public meta import CFSG.RankThree.PartOne.KS.RuFiveData
public meta import CFSG.RankThree.PartOne.KS.RuFiveAux
public meta import CFSG.RankThree.Native.HSMcLFiveCheck
public meta import CFSG.RankThree.Native.FiveKit
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.Sporadic.Schreier.RuDefs
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum

public noncomputable section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Sporadic.RuSchreier

theorem ruFive_Q_check :
    linesOK 4060 ruFiveQGens ruFiveKeys ruFiveQCert ruFiveLines = true ∧
      allLt ruFiveQGens.size
        (fun l => siftA 4060 ruPLevels ruCase0BaseArr 0 ruFiveQGens[l]!) = true ∧
      transOK 4060 ruFiveTransporters ruFiveLines ruFiveRec ruPLevels ruCase0BaseArr = true ∧
      ruFiveRec.getD 0 0 = 0 ∧ ruFiveRec.getD 1 0 = 1 ∧
      allLt 31 (fun j => ruFiveRec.getD j 0 == 0 || ruFiveRec.getD j 0 == 1) = true :=
  Certificates.certificate10057.1

theorem ruFive_case0_check :
    caseChainOK2 4060 ruCase0Arrs ruCase0BaseArr ruCase0Words (ruArr4060 0) (ruArr4060 1) =
        true ∧
      rawOrbitSizes 4060 ruCase0Arrs ruCase0BaseArr = [4060, 1755, 1024, 4, 5, 1, 1, 1, 1] ∧
      validA 4060 (ruArr4060 0) = true ∧ validA 4060 (ruArr4060 1) = true ∧
      centOK 4060 ruCase0Arrs ruCase0BaseArr ruFiveLines[0]! ruCase0Rels ruFiveC0Gens ruFiveKeys
        ruFiveC0Cert 1000 = true ∧
      normalOK 4060 ruFiveC0Gens ruFiveA0Gens ruFiveKeys ruFiveC0Cert ruFiveA0Cert 125 ruPLevels
        ruCase0BaseArr = true ∧
      zCentOK 4060 ruFiveA0Gens ruFiveC0Cert ruFiveA0Cert ruFiveLines[0]! = true ∧
      eqA 4060 ruFiveC0Gens[0]! ruFiveLines[0]! = true :=
  Certificates.certificate10057.2.1

theorem ruFive_case1_check :
    caseChainOK2 4060 ruCase1Arrs ruCase1BaseArr ruCase1Words (ruArr4060 0) (ruArr4060 1) =
        true ∧
      centOK 4060 ruCase1Arrs ruCase1BaseArr ruFiveLines[1]! ruCase1Rels ruFiveC1Gens ruFiveKeys
        ruFiveC1Cert 300 = true ∧
      derivedOK 4060 ruFiveC1Gens ruFiveDGens ruFiveKeys ruFiveC1Cert ruFiveDCert ruFiveDWit[0]!
        ruFiveDWit[1]! ruFiveLines[1]! ruPLevels ruCase0BaseArr = true ∧
      eqA 4060 ruFiveC1Gens[0]! ruFiveLines[1]! = true :=
  Certificates.certificate10057.2.2

end CFSG.RankThree.PartOne
