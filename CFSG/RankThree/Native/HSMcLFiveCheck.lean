module

public import CFSG.RankThree.Native.HSMcLFiveData
public import CFSG.RankThree.Native.HSMcLFiveAux
public import CFSG.RankThree.Native.HSMcLSmallCheck
public import CFSG.RankThree.Native.FiveKit
public import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import CFSG.RankThree.Native.HSMcLFiveData
public meta import CFSG.RankThree.Native.HSMcLFiveAux
public meta import CFSG.RankThree.Native.HSMcLSmallCheck
public meta import CFSG.RankThree.Native.HSMcLSmallData
public meta import CFSG.RankThree.Native.HSMcLAuxData
public meta import CFSG.RankThree.Native.FiveKit
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public import Certificates.Certificate8128

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier

theorem hs100Five_Q_check :
    linesOK 100 hs100FiveQGens hs100FiveKeys hs100FiveQCert hs100FiveLines = true ∧
      allLt hs100FiveQGens.size
        (fun l => siftA 100 hs100PLevels hs100BaseArr 0 hs100FiveQGens[l]!) = true ∧
      transOK 100 hs100FiveTransporters hs100FiveLines hs100FiveRec hs100RLevels
        hs100RBaseArr = true ∧
      hs100FiveRec.getD 0 0 = 0 ∧ hs100FiveRec.getD 2 0 = 2 ∧ hs100FiveRec.getD 23 0 = 23 ∧
      allLt 31 (fun j => hs100FiveRec.getD j 0 == 0 || hs100FiveRec.getD j 0 == 2 ||
        hs100FiveRec.getD j 0 == 23) = true :=
  Certificates.certificate8128.1

theorem hs100Five_case0_check :
    caseChainOK 100 hs100Case0Arrs hs100Case0BaseArr hs100Case0Words (hs100Arr 0) (hs100Arr 1)
        (hs100Arr 15) = true ∧
      centOK 100 hs100Case0Arrs hs100Case0BaseArr hs100FiveLines[0]! hs100Case0Rels
        hs100FiveC0Gens hs100FiveKeys hs100FiveC0Cert 50 = true ∧
      normalOK 100 hs100FiveC0Gens hs100FiveA0Gens hs100FiveKeys hs100FiveC0Cert hs100FiveA0Cert
        25 hs100PLevels hs100BaseArr = true ∧
      selfCentOK 100 hs100FiveA0Gens hs100FiveC0Cert hs100FiveA0Cert = true ∧
      eqA 100 hs100FiveC0Gens[0]! hs100FiveLines[0]! = true :=
  Certificates.certificate8128.2.1

theorem hs100Five_case2_check :
    caseChainOK 100 hs100Case2Arrs hs100Case2BaseArr hs100Case2Words (hs100Arr 0) (hs100Arr 1)
        (hs100Arr 15) = true ∧
      centOK 100 hs100Case2Arrs hs100Case2BaseArr hs100FiveLines[2]! hs100Case2Rels
        hs100FiveC2Gens hs100FiveKeys hs100FiveC2Cert 600 = true ∧
      derivedOK 100 hs100FiveC2Gens hs100FiveDGens hs100FiveKeys hs100FiveC2Cert hs100FiveDCert
        hs100FiveDWit[0]! hs100FiveDWit[1]! hs100FiveLines[2]! hs100PLevels hs100BaseArr = true ∧
      eqA 100 hs100FiveC2Gens[0]! hs100FiveLines[2]! = true :=
  Certificates.certificate8128.2.2.1

theorem hs100Five_case23_check :
    caseChainOK 100 hs100Case23Arrs hs100Case23BaseArr hs100Case23Words (hs100Arr 0)
        (hs100Arr 1) (hs100Arr 15) = true ∧
      centOK 100 hs100Case23Arrs hs100Case23BaseArr hs100FiveLines[23]! hs100Case23Rels
        hs100FiveC23Gens hs100FiveKeys hs100FiveC23Cert 1000 = true ∧
      normalOK 100 hs100FiveC23Gens hs100FiveA23Gens hs100FiveKeys hs100FiveC23Cert
        hs100FiveA23Cert 125 hs100PLevels hs100BaseArr = true ∧
      zCentOK 100 hs100FiveA23Gens hs100FiveC23Cert hs100FiveA23Cert hs100FiveLines[23]! = true ∧
      eqA 100 hs100FiveC23Gens[0]! hs100FiveLines[23]! = true :=
  Certificates.certificate8128.2.2.2.1

theorem mcl275Five_Q_check :
    linesOK 275 mcl275FiveQGens mcl275FiveKeys mcl275FiveQCert mcl275FiveLines = true ∧
      allLt mcl275FiveQGens.size
        (fun l => siftA 275 mcl275PLevels PairMcL.baseArr 0 mcl275FiveQGens[l]!) = true ∧
      transOK 275 mcl275FiveTransporters mcl275FiveLines mcl275FiveRec mcl275RLevels
        mcl275RBaseArr = true ∧
      mcl275FiveRec.getD 0 0 = 0 ∧ mcl275FiveRec.getD 1 0 = 1 ∧
      allLt 31 (fun j => mcl275FiveRec.getD j 0 == 0 || mcl275FiveRec.getD j 0 == 1) = true :=
  Certificates.certificate8128.2.2.2.2.1

theorem mcl275Five_case0_check :
    caseChainOK 275 mcl275Case0Arrs mcl275Case0BaseArr mcl275Case0Words mclStrongArrs[0]!
        mclStrongArrs[1]! (CFSG.Sporadic.SmallOddCore.Native.natArr
          CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true ∧
      centOK 275 mcl275Case0Arrs mcl275Case0BaseArr mcl275FiveLines[0]! mcl275Case0Rels
        mcl275FiveC0Gens mcl275FiveKeys mcl275FiveC0Cert 50 = true ∧
      normalOK 275 mcl275FiveC0Gens mcl275FiveA0Gens mcl275FiveKeys mcl275FiveC0Cert
        mcl275FiveA0Cert 25 mcl275PLevels PairMcL.baseArr = true ∧
      selfCentOK 275 mcl275FiveA0Gens mcl275FiveC0Cert mcl275FiveA0Cert = true ∧
      eqA 275 mcl275FiveC0Gens[0]! mcl275FiveLines[0]! = true :=
  Certificates.certificate8128.2.2.2.2.2.1

theorem mcl275Five_case1_check :
    caseChainOK 275 mcl275Case1Arrs mcl275Case1BaseArr mcl275Case1Words mclStrongArrs[0]!
        mclStrongArrs[1]! (CFSG.Sporadic.SmallOddCore.Native.natArr
          CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true ∧
      centOK 275 mcl275Case1Arrs mcl275Case1BaseArr mcl275FiveLines[1]! mcl275Case1Rels
        mcl275FiveC1Gens mcl275FiveKeys mcl275FiveC1Cert 1500 = true ∧
      normalOK 275 mcl275FiveC1Gens mcl275FiveA1Gens mcl275FiveKeys mcl275FiveC1Cert
        mcl275FiveA1Cert 125 mcl275PLevels PairMcL.baseArr = true ∧
      zCentOK 275 mcl275FiveA1Gens mcl275FiveC1Cert mcl275FiveA1Cert mcl275FiveLines[1]! = true ∧
      eqA 275 mcl275FiveC1Gens[0]! mcl275FiveLines[1]! = true :=
  Certificates.certificate8128.2.2.2.2.2.2

end CFSG.RankThree.Native
