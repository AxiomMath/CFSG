
module

public import Certificates.Certificate2283Base

public import CFSG.Sporadic.SmallOddCore.J3WordBoundInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.SporSch.PairJ3.Check2283

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native in
theorem certificate2283 : (ordB PairJ3.bs (patW PairJ3.wA PairJ3.wB j3WPat) 17 = true)
    ∧ (PairJ3.parCount (pairPred PairJ3.bs 3 PairJ3.wA j3WConds) PairJ3.blocks = 3840) := KernelSporSch.PJ3W2283.facts

end Certificates
