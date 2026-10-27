
module

public import Certificates.Certificate2225Base
import all Certificates.Certificate2225Base

public import CFSG.Sporadic.Schreier.PairHeCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
import Certificates.Kernel.SporSch.PairHe.Cnt2225

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairHe in
open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB in
theorem certificate2225 : countPair CFSG.Sporadic.Schreier.PairHe.bs 7 wA conds heBlocks ≤ 322560 ∧
    (List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346 ∧
    (List.range 8330).countP (fun i => t1Arr[i]! == i) = 42 := KernelSporSch.PHePart.facts

end Certificates
