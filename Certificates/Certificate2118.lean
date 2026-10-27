
module

public import Certificates.Certificate2118Base

public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import Certificates.Kernel.SporSch.HeT.Facts2118
import CFSG.Sporadic.HeldB.CertPChainData
import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Sporadic.HeldB.OuterArithCheckInputs
meta import CFSG.Sporadic.HeldB.AutData
meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native in
theorem certificate2118 : (heUArr[0]! = 0)
    ∧ ((heGen 0)[0]! = 0)
    ∧ ((List.range 8330).countP (fun i => heUArr[i]! == i) = 98)
    ∧ ((List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346)
    ∧ (eqA 8330 (hePowA (heGen 0) 2) (CFSG.Monster.B.Co2.Native.idA 8330) = true)
    ∧ (eqA 8330 (hePowA (heGen 1) 7) (CFSG.Monster.B.Co2.Native.idA 8330) = true)
    ∧ (((heBlock1.all fun t => t[0]! == 0) && (heBlock2.all fun t => t[0]! == 0) &&
      countWPar 25 (commB heUArr heBase) (heBlock0.filter fun t0 => heUArr[t0[0]!]! == t0[0]!)
        [heBlock1, heBlock2] == 15120 &&
      countWPar 1 (twistInvB heUArr heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 3136) = true
    ) := KernelSporSch.HeF18.facts

end Certificates
