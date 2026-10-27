module

public import CFSG.Sporadic.J4.QT2LocCntNative

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def chkFix2B : Bool :=
  let T := uTab (locMats ()) (locInvs ())
  (List.range' 1 4).all fun l =>
    let v := pathVec (repPaths.getD l [])
    tMasks.all fun c => differs (frApply (frTable (etaRows T 11 c)) v) v

@[expose] def chkFix2A : Bool :=
  let T := uTab (locMats ()) (locInvs ())
  (List.range' 2 2).all fun l =>
    let v := pathVec (repPaths.getD l [])
    zMasks.all fun c => differs (frApply (frTable (etaRows T 11 c)) v) v

end CFSG.Sporadic.J4.QT2
