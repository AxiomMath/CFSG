module

public import CFSG.Sporadic.Schreier.TitsInvCheck
public import CFSG.RankThree.PartOne.KE.TitsFiveCheckInputs
public import Certificates.Certificate10050
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import CFSG.Sporadic.Schreier.TitsInvCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

theorem titsFive_check :
    lettersOK 13 titsFiveWord = true ∧ inH titsFiveArr = true ∧
    eqA 1755 titsFiveArr (idA 1755) = false ∧
    eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 titsFiveArr titsFiveArr)
      titsFiveArr) titsFiveArr) titsFiveArr) (idA 1755) = true ∧
    all5 1755 titsHLevels (fun a => !commA a titsFiveArr || anyEq titsCH5 a) = true ∧
    titsCH5.length = 10 ∧
    titsCH5.all (fun c => isInvA 1755 c (invCand 1755 c) && commA c titsFiveArr && inH c) = true ∧
    titsCH5.Pairwise (fun a b => eqA 1755 a b = false) :=
  Certificates.certificate10050

end CFSG.RankThree.PartOne.KE
