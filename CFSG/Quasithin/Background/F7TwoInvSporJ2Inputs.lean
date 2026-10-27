module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Quasithin.F7Two

open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native

@[expose] def j2CommB (t : Array Nat) : Array Nat :=
  compA 315 (compA 315 (compA 315 t autStrong[1]!) t) (invCand 315 autStrong[1]!)

@[expose] def j2OrderThree (t : Array Nat) : Bool :=
  eqA 315 (compA 315 t (compA 315 t t)) (idA 315) && !eqA 315 t (idA 315)

@[expose] def j2InvChk (_ : Unit) : Bool :=
  eqA 315 (compA 315 outerArr autStrong[0]!) (compA 315 autStrong[0]! outerArr) &&
    eqA 315 (compA 315 twoAArr autStrong[0]!) (compA 315 autStrong[0]! twoAArr) &&
    j2OrderThree (j2CommB outerArr) && j2OrderThree (j2CommB twoAArr)

end CFSG.Quasithin.F7Two
