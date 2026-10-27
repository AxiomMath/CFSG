module

public import CFSG.Sporadic.J4.QT2LocCntNative
public import CFSG.Sporadic.J4.QT2LocX0Native

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def rep5Vec : V2 := pathVec (repPaths.getD 5 [])

@[expose] def orb5 : VOrb := vorbit locTabs rep5Vec 15180 15

@[expose] def fixedIn (M : Array V2) (O : VOrb) : List V2 :=
  let T := frTable M
  (O.pts.filter fun v => (frApply T v).beq v).toList

@[expose] def fixEta (c : Nat) : List V2 :=
  rootV :: (fixedIn (etaE c) orb5 ++ fixedIn (etaE c) orb6)

@[expose] def chkOrb5 : Bool := vorbOK locTabs rep5Vec orb5 15180

@[expose] def chkEtaOneWf : Bool := wfRows (etaE 1)

@[expose] def chkFixEtaOne : Bool :=
  (fixEta 1).length == 8317 && (fixEta 1).eraseDups.length == 8317

end CFSG.Sporadic.J4.QT2
