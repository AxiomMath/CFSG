module

public import CFSG.RankThree.PartOne.KS.HeFiveData
public import CFSG.RankThree.PartOne.KS.HeFiveAux
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
public import Certificates.Certificate10051
public meta import CFSG.RankThree.PartOne.KS.HeFiveData
public meta import CFSG.RankThree.PartOne.KS.HeFiveAux
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
public meta import Mathlib
public import Mathlib

public noncomputable section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Sporadic.HeldB

theorem heFive_Q_check :
    linesOKG 5 25 6 8330 heFiveQGens heFiveKeys heFiveQCert heFiveLines = true ∧
      allLt heFiveQGens.size (fun l => siftA 8330 heLevels heBase.toArray 0 heFiveQGens[l]!) =
        true ∧
      transOKG 6 8330 heFiveTransporters heFiveLines heFiveRec heFiveRLevels heFiveCase0BaseArr =
        true ∧
      allLt 6 (fun j => (List.range 1).any fun i => heFiveRec.getD j 0 == i) = true ∧
      heFiveRec.getD 0 0 = 0 :=
  Certificates.certificate10051.1

theorem heFive_case0_check :
    caseChainOK3 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveCase0Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 5 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveLines[0]! heFiveCase0Rels
        heFiveC0Gens heFiveKeys heFiveC0Cert 600 = true ∧
      eqA 8330 heFiveC0Gens[0]! heFiveLines[0]! = true ∧
      derivedOKP 5 60 8330 heFiveC0Gens heFiveDGens0 heFiveKeys heFiveC0Cert heFiveDCert0
        heFiveDWit0[0]! heFiveDWit0[1]! heFiveLines[0]! heLevels heBase.toArray = true :=
  Certificates.certificate10051.2

end CFSG.RankThree.PartOne
