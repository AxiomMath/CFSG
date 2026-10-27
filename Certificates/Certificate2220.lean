
module

public import Certificates.Certificate2220Base

public import CFSG.Sporadic.Schreier.PairHSCheck
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.SporSch.PairHS.Check2220
import CFSG.Certificates.Kernel.SporSch.PairClTSound

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairHS in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2220 : (parCount (ordPred CFSG.Sporadic.Schreier.PairHS.bs 2) blocks = 21175)
    ∧ (parCount (ordPred CFSG.Sporadic.Schreier.PairHS.bs 5) blocks = 2010624)
    ∧ ((cl.map fun c => c.2.1.size * parCount (pairPred CFSG.Sporadic.Schreier.PairHS.bs 5 c.1 conds) blocks).sum =
      1064448000
    ) := KernelSporSch.PHSCount.facts

end Certificates
