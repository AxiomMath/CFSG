
module

public import Certificates.Certificate2274Base

public import CFSG.Sporadic.SmallOddCore.HSWordBoundInputs
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.SporSch.PairHS.Check2274
import CFSG.Certificates.Kernel.SporSch.PairClTSound

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native in
theorem certificate2274 : (ordB PairHS.bs (patW PairHS.wA PairHS.wB [false, true, true]) 10 = true)
    ∧ (countPair PairHS.bs 5 PairHS.wA hsWConds PairHS.blocks = 15360) := KernelSporSch.PHS2274.facts

end Certificates
