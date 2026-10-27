module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def hsThreeBase : Array Tab :=
  Array.ofFn (n := 5) fun k => natArr (hsCentTbl (k.val + 21))

@[expose] def hsThreeX0Word : List Nat := [3, 2, 4, 3, 4, 2, 4, 1, 3]

@[expose] def hsThreeWords : List (List Nat) := [[0], [4, 1], [3, 4, 1, 3, 2]]

@[expose] def hsThreeGens : Array Tab :=
  Array.ofFn (n := 3) fun j => wordTabS 3850 hsThreeBase (hsThreeWords.getD j.val [])

@[expose] def hsThreeEnum : Enum := enumBFS 3850 hsThreeGens 720

end CFSG.Sporadic.SmallOddCore
