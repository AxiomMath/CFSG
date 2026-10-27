
module

public import Certificates.Certificate2224Base
import all Certificates.Certificate2224Base

public import CFSG.Sporadic.Schreier.PairHeCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairHeCheck
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.SporSch.PairHe.Check2224

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairHe in
open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB in
theorem certificate2224 : countOrd CFSG.Sporadic.Schreier.PairHe.bs 2 heBlocks = 212415 := KernelSporSch.PHeCount.facts

end Certificates
