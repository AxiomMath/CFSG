module

public import CFSG.Sporadic.Schreier.TitsLocalCheck
public import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import Certificates.Certificate2263

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsCentral_check :
    titsSBase.length = 5 ∧ titsHBase.length = 5 ∧ titsNBase.length = 5 ∧
    all5 1755 titsSLevels (fun a => !(commutesAll 1755 a (titsSArrs.extract 0 3)) ||
      eqA 1755 a (idA 1755) || eqA 1755 a titsZArr) = true ∧
    all5 1755 titsHLevels (fun a => !(commutesAll 1755 a (titsJArrs.extract 0 4)) ||
      anyEq titsCHJ a) = true ∧
    all5 1755 titsNLevels (fun a => !(commutesAll 1755 a (titsKArrs.extract 0 2)) ||
      anyEq titsCNK a) = true ∧
    titsCHJ.length = 2 ∧ titsCNK.length = 4 ∧
    titsCHJ.all (fun c => isInvA 1755 c (invCand 1755 c) &&
      commutesAll 1755 c (titsJArrs.extract 0 4) &&
      siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 c &&
      siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 c) = true ∧
    titsCNK.all (fun c => isInvA 1755 c (invCand 1755 c) &&
      commutesAll 1755 c (titsKArrs.extract 0 2) &&
      siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 c &&
      siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 c) = true ∧
    titsCHJ.Pairwise (fun a b => eqA 1755 a b = false) ∧
    titsCNK.Pairwise (fun a b => eqA 1755 a b = false) ∧
    isInvA 1755 titsZArr (invCand 1755 titsZArr) = true ∧
    siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 titsZArr = true ∧
    eqA 1755 titsZArr (idA 1755) = false ∧
    eqA 1755 (compA 1755 titsZArr titsZArr) (idA 1755) = true ∧
    commutesAll 1755 titsZArr (titsSArrs.extract 0 3) = true ∧
    commutesAll 1755 titsZArr (titsHArrs.extract 0 3) = true :=
  Certificates.certificate2263

end CFSG.Sporadic.Schreier.Tits
