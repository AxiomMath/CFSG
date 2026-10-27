module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F3.Native
open CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27 CFSG.Sporadic.FischerOddCore.Native
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiNative

set_option compiler.extract_closed false

@[expose] def fixCount22 (T : Table) : Nat :=
  ((List.range 3510).filter fun i => ap T i == i).length

@[expose] def fi22RepFixOK (O : COrbit) : Bool :=
  let G := genT O
  let P := par ()
  fixCount22 (eltT P G globRep[0]!) == 0 && fixCount22 (eltT P G globRep[1]!) == 27 &&
    fixCount22 (eltT P G globRep[2]!) == 36 && fixCount22 (eltT P G globRep[3]!) == 126

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
