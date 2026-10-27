
module

public import CFSG.Sporadic.Co2Schreier.CoreCheckBase

public import CFSG.Sporadic.Co2Schreier.ChainCheck
public import Std.Data.HashMap
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public import Certificates.Certificate2051

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

theorem coreQ_check :
    coreOK qArrs cArrs localRec.chains.qAction.origArrs 512 [0, 23] enumQ = true ∧
    eqA 2300 enumQ.elems[23]! zArr = true :=
  Certificates.certificate2051.1

theorem coreR_check :
    coreOK rArrs dArrs localRec.chains.rAction.origArrs 2048 centerIdxR enumR = true ∧
    eqA 2300 enumR.elems[617]! zArr = true ∧ eqA 2300 enumR.elems[434]! tArr = true :=
  Certificates.certificate2051.2.1

theorem chainQAction_check : recordOK 512 localRec.chains.qAction 4 = true ∧
    recordOrbits 512 localRec.chains.qAction = [270, 28, 64, 24, 4, 2, 2, 2] :=
  Certificates.certificate2051.2.2.1

theorem chainRAction_check : recordOK 2048 localRec.chains.rAction 4 = true ∧
    recordOrbits 2048 localRec.chains.rAction = [840, 8, 6, 4, 2, 2, 2] :=
  Certificates.certificate2051.2.2.2

end CFSG.Sporadic.Co2Schreier
