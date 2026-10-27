module

public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public import Certificates.Certificate10055
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
public import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Mathlib
public import Mathlib

public noncomputable section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Sporadic.HeldB

theorem heSeven_Q_check :
    linesOKG 7 343 57 8330 heSevenQGens heSevenKeys heSevenQCert heSevenLines = true ∧
      allLt heSevenQGens.size (fun l => siftA 8330 heLevels heBase.toArray 0 heSevenQGens[l]!) =
        true ∧
      transOKG 57 8330 heSevenTransporters heSevenLines heSevenRec heSevenRLevels
        heSevenCase0BaseArr = true ∧
      allLt 57 (fun j => (List.range 3).any fun i => heSevenRec.getD j 0 == i) = true ∧
      heSevenRec.getD 0 0 = 0 ∧
      heSevenRec.getD 1 0 = 1 ∧
      heSevenRec.getD 2 0 = 2 :=
  Certificates.certificate10055

end CFSG.RankThree.PartOne
