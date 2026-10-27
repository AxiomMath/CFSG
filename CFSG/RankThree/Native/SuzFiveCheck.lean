module

public import CFSG.RankThree.Native.SuzFiveDefs
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.RankThree.Native.SuzFiveDefs
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public meta import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import CFSG.RankThree.Native.SuzFiveCheckInputs
public import Certificates.Certificate8147

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore

theorem suzFive_Q_check :
    suzFiveQCheck suzFiveQCert suzFiveLines = true :=
  Certificates.certificate8147.1

theorem suzFive_C_check :
    (∀ i < 6, suzFiveCCheck (suzFiveCArrs i) (suzFiveLineArr i) (suzFiveCCert i)
      suzFiveCentOrders[i]! = true) :=
  Certificates.certificate8147.2.1

theorem suzFive_D_check_0 :
    suzFiveDCheck (suzFiveCArrs 0) (suzFiveCCert 0) (suzFiveDArrs 0)
    (suzFiveDCert 0) 360 (suzFiveLineArr 0) 5 = true :=
  Certificates.certificate8147.2.2.1

theorem suzFive_D_check_1 :
    suzFiveDCheck (suzFiveCArrs 1) (suzFiveCCert 1) (suzFiveDArrs 1)
    (suzFiveDCert 1) 60 (suzFiveLineArr 1) 10 = true :=
  Certificates.certificate8147.2.2.2.1

theorem suzFive_D_check_2 :
    suzFiveDCheck (suzFiveCArrs 2) (suzFiveCCert 2) (suzFiveDArrs 2)
    (suzFiveDCert 2) 60 (suzFiveLineArr 2) 10 = true :=
  Certificates.certificate8147.2.2.2.2.1

theorem suzFive_D_check_3 :
    suzFiveDCheck (suzFiveCArrs 3) (suzFiveCCert 3) (suzFiveDArrs 3)
    (suzFiveDCert 3) 360 (suzFiveLineArr 3) 5 = true :=
  Certificates.certificate8147.2.2.2.2.2.1

theorem suzFive_D_check_4 :
    suzFiveDCheck (suzFiveCArrs 4) (suzFiveCCert 4) (suzFiveDArrs 4)
    (suzFiveDCert 4) 360 (suzFiveLineArr 4) 5 = true :=
  Certificates.certificate8147.2.2.2.2.2.2.1

theorem suzFive_D_check_5 :
    suzFiveDCheck (suzFiveCArrs 5) (suzFiveCCert 5) (suzFiveDArrs 5)
    (suzFiveDCert 5) 60 (suzFiveLineArr 5) 10 = true :=
  Certificates.certificate8147.2.2.2.2.2.2.2.1

theorem suzFive_pairs_check : ∀ i < 6, suzFivePairsCheck i = true :=
  Certificates.certificate8147.2.2.2.2.2.2.2.2.1

theorem suzFive_orbit_check :
    ∀ i < 6, suzFiveOrbitCheck (suzFiveDArrs i) suzFiveOrbits[i]! suzFiveOrbits[i]!.length
      suzFiveDerivedOrders[i]! (suzFiveOrbitCert i) = true :=
  Certificates.certificate8147.2.2.2.2.2.2.2.2.2.1

theorem suzFive_graph_check :
    ∀ i < 6, suzFiveGraphCheck (suzFiveLineArr i) suzFiveInit[i]! suzFiveSteps[i]! = true :=
  Certificates.certificate8147.2.2.2.2.2.2.2.2.2.2

end CFSG.RankThree.Native
