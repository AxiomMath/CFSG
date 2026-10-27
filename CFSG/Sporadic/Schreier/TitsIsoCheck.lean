module

public import CFSG.Sporadic.Schreier.TitsCertCheck
public import Certificates.Data.CFSGNative.SectionRank.TitsChain
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import Certificates.Data.CFSGNative.SectionRank.TitsChain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Certificate2267

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Monster.B.Co2.Native

theorem titsSigma_check :
    isInvA 1755 titsSigmaArr (invCand 1755 titsSigmaArr) = true ∧
    CFSG.SectionRank.Native.Tits.genTables.size = 4 ∧
    (∀ s < 4, ∀ i < 1755, titsSigmaArr[
      CFSG.Sporadic.Th.Native.ap CFSG.SectionRank.Native.Tits.genTables[s]! i]! =
        (titsGenArrs[s]!)[titsSigmaArr[i]!]!) :=
  Certificates.certificate2267

end CFSG.Sporadic.Schreier.Tits
