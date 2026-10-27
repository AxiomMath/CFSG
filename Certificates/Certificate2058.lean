module

public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Schreier.WitText
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Certificates.Kernel.SporSch.Co2SShapeSound
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Co2Schreier.TextCheck

public section

namespace Certificates

open CFSG.KS.Co2Shape CFSG.KS.Co2SShape CFSG.Sporadic.Co2Schreier

set_option maxRecDepth 100000 in
theorem sixChainK : chainK witRec.wLocal.sixActionChain 63 2 12 [0, 1, 3, 7, 15, 31] = true := by
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Mathieu in
open scoped Matrix in
theorem certificate2058 : chainShapeOK witRec.wLocal.sixActionChain 63 2 12 [0, 1, 3, 7, 15, 31] = true := chainK_sound sixChainK

end Certificates
