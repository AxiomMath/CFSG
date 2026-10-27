
module

public import Certificates.Certificate2238Base

public import CFSG.Sporadic.Schreier.PairJ3Check
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.SporSch.PairJ3.Check2238

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3 in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2238 : (parCount (ordPred CFSG.Sporadic.Schreier.PairJ3.bs 2) blocks = 26163)
    ∧ (parCount (ordPred CFSG.Sporadic.Schreier.PairJ3.bs 3) blocks = 253232)
    ∧ ((cl.map fun c => c.2.1.size * parCount (pairPred CFSG.Sporadic.Schreier.PairJ3.bs 3 c.1 conds) blocks).sum =
      301397760
    ) := KernelSporSch.PJ3Count.facts

end Certificates

end
