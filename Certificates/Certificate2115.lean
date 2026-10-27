
module

public import Certificates.Certificate2115Base

public import CFSG.Sporadic.HeldB.InnerClassCheckInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import Certificates.Kernel.SporSch.HeT.Facts2115
import CFSG.Sporadic.HeldB.CertPChainData
import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native in
theorem certificate2115 : ((List.range 8330).countP (fun i => heT1Arr[i]! == i) = 42)
    ∧ (heT1cArr[0]! = 0)
    ∧ ((countWPar 87 (commB (heGen 0) heBase)
        (heBlock0.filter fun t0 => (heGen 0)[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 161280 &&
      countWPar 11 (commB heT1cArr heBase)
        (heBlock0.filter fun t0 => heT1cArr[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 21504 &&
      countWPar 1 (twistInvB (idA 8330) heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 1984) = true
    ) := KernelSporSch.HeF15.facts

end Certificates
