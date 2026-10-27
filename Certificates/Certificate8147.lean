module

public import CFSG.RankThree.Native.SuzFiveDefs
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import CFSG.RankThree.Native.SuzFiveCheckInputs
import Certificates.Kernel.Sporadic.OddCore.S8147Fin
import Certificates.Kernel.Sporadic.OddCore.S8147Neg
import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Refine
meta import Certificates.Data.CFSGNative.Perm.Chain
import CFSG.Sporadic.HNOddCore.FourPairA

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Fischer in
theorem certificate8147 : (suzFiveQCheck suzFiveQCert suzFiveLines = true)
    ∧ (

    (∀ i < 6, suzFiveCCheck (suzFiveCArrs i) (suzFiveLineArr i) (suzFiveCCert i)
      suzFiveCentOrders[i]! = true)
)
    ∧ (
 suzFiveDCheck (suzFiveCArrs 0) (suzFiveCCert 0) (suzFiveDArrs 0)
    (suzFiveDCert 0) 360 (suzFiveLineArr 0) 5 = true
)
    ∧ (
 suzFiveDCheck (suzFiveCArrs 1) (suzFiveCCert 1) (suzFiveDArrs 1)
    (suzFiveDCert 1) 60 (suzFiveLineArr 1) 10 = true
)
    ∧ (
 suzFiveDCheck (suzFiveCArrs 2) (suzFiveCCert 2) (suzFiveDArrs 2)
    (suzFiveDCert 2) 60 (suzFiveLineArr 2) 10 = true
)
    ∧ (
 suzFiveDCheck (suzFiveCArrs 3) (suzFiveCCert 3) (suzFiveDArrs 3)
    (suzFiveDCert 3) 360 (suzFiveLineArr 3) 5 = true
)
    ∧ (
 suzFiveDCheck (suzFiveCArrs 4) (suzFiveCCert 4) (suzFiveDArrs 4)
    (suzFiveDCert 4) 360 (suzFiveLineArr 4) 5 = true
)
    ∧ (
 suzFiveDCheck (suzFiveCArrs 5) (suzFiveCCert 5) (suzFiveDArrs 5)
    (suzFiveDCert 5) 60 (suzFiveLineArr 5) 10 = true
)
    ∧ (∀ i < 6, suzFivePairsCheck i = true)
    ∧ (

    ∀ i < 6, suzFiveOrbitCheck (suzFiveDArrs i) suzFiveOrbits[i]! suzFiveOrbits[i]!.length
      suzFiveDerivedOrders[i]! (suzFiveOrbitCert i) = true
)
    ∧ (∀ i < 6, suzFiveGraphCheck (suzFiveLineArr i) suzFiveInit[i]! suzFiveSteps[i]! = true) := KernelSpor.S8147.facts8147

end Certificates
