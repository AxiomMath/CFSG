module

public import CFSG.Sporadic.HNOddCore.InvArrays
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native InvData

@[expose] def allSize (A : Array (Array Nat)) (m : Nat) : Bool := A.all fun a => a.size == m

@[expose] def allLength (A : Array (List Int)) (m : Nat) : Bool := A.all fun a => a.length == m

@[expose] def fixSizesOK : Bool :=
  f1Arr.size == 1156 && f4Arr.size == 800 && f6Arr.size == 8800 && f1Arr[0]! == 0 &&
    f4Arr[0]! == 0 && f6Arr[0]! == 0 && (o1Lists[0]!)[0]! == 0 && (o6Lists[0]!)[0]! == 0

@[expose] def actSizesOK : Bool :=
  s1Perms.size == 9 && allSize s1Perms 1156 && s4Perms.size == 11 && allSize s4Perms 800 &&
    s6Perms.size == 12 && allSize s6Perms 8800

@[expose] def twoSizesOK : Bool :=
  cstrongPerms.size == 20 && allSize cstrongPerms 800 && qPerms.size == 8 && allSize qPerms 800 &&
    cparRecs.size == 14400 && allLength cparRecs 2 && cleftTabs.size == 11 &&
    allSize cleftTabs 14400 && vparRecs.size == 4608 && allLength vparRecs 2 &&
    vleftTabs.size == 10 && allSize vleftTabs 4608

@[expose] def sylowSizesOK : Bool :=
  pgenPerms.size == 14 && allSize pgenPerms 800 && parRecs.size == 16384 &&
    allLength parRecs 2 && pleftTabs.size == 14 && allSize pleftTabs 16384 &&
    pconjPerms.size == 6 && allSize pconjPerms 256 && clsLists.size == 29 &&
    (clsLists.foldl (fun s a => s + a.size) 0) == 880 && witRep.size == 39 && nonRep.size == 9

@[noinline, expose] def dataChecks : Bool := fixSizesOK && actSizesOK && twoSizesOK && sylowSizesOK

end CFSG.Sporadic.HNOddCore.Native
