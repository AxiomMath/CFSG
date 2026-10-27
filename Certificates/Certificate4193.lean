module

public import CFSG.Quasithin.EmptyFaithful.F112SInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public meta import CFSG.Quasithin.Recognition.CertDataTitsOuter
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Quasithin.EmptyFaithful.F112SInputs
public import Certificates.Kernel.SporSch.Tits.Glue4193
public import Certificates.Kernel.Sporadic.Tits.GroupT2264

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.F112S in
theorem certificate4193 : invsOK = true ∧ invsDistinct = true ∧ invsComplete = true ∧
    search numInvs prodAt 6 [] 0 = true ∧ outerOK = true :=
  KernelSporSch.Rank4193.titsRankCheck_k

end Certificates
