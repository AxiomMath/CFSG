module

public import CFSG.Sporadic.HeldB.CertPBridgeData
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.He.Certificate
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.HeldB.CertPBridgeData
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.He.Certificate
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

@[expose] def heBridgeOK : Bool :=
  let O := orbitData ()
  isInvA 8330 heBridgeArr (invCand 8330 heBridgeArr) &&
    allLt 8330 (fun i => ap O.alpha heBridgeArr[i]! == heBridgeArr[(heGen 0)[i]!]!) &&
    allLt 8330 (fun i => ap O.beta heBridgeArr[i]! == heBridgeArr[(heGen 1)[i]!]!)

end CFSG.Sporadic.HeldB
