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
import Certificates.Kernel.SporSch.Tits.Iso2267

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native in
theorem certificate2267 : isInvA 1755 titsSigmaArr (invCand 1755 titsSigmaArr) = true ∧
    CFSG.SectionRank.Native.Tits.genTables.size = 4 ∧
    (∀ s < 4, ∀ i < 1755, titsSigmaArr[
      CFSG.Sporadic.Th.Native.ap CFSG.SectionRank.Native.Tits.genTables[s]! i]! =
        (titsGenArrs[s]!)[titsSigmaArr[i]!]!) := KernelSporSch.TitsIso.facts

end Certificates
