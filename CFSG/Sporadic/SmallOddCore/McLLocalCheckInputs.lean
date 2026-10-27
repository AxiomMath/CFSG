module

public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native

@[expose] def mclT0Arr : Array Nat := natArr (mclCentTbl 4)

@[expose] def mclFix : List Nat := fixedList 275 mclT0Arr

@[expose] def mclXGens : Array Tab :=
  Array.ofFn (n := 2) fun k => restrictArr mclFix (natArr (mclCentTbl (k.val + 5)))

@[expose] def mclXInvs : Array Tab := mclXGens.map (invTab 35)

@[expose] def mclXWords : List (List Nat) :=
  [[], [0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0], [1, 1, 1, 1, 1, 1, 0, 1, 0],
    [1, 1, 1, 1, 1, 0, 1, 1, 0], [1, 1, 1, 1, 0, 1, 0, 1, 0], [1, 0], [1, 1, 0], [1, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 0], [1, 1, 1, 0, 1, 0, 1, 0], [1], [1, 1, 1], [1, 1, 1, 0, 1, 1, 0]]

@[expose] def mclXSizes : List Nat :=
  [1, 105, 112, 210, 1120, 1260, 1344, 1344, 1344, 1680, 2520, 2880, 2880, 3360]

@[expose] def mclXEnum : Enum := enumBFS 35 mclXGens 20160

@[expose] def mclXOrbits : Array Enum :=
  Array.ofFn (n := 14) fun l => orbitBFS 35 mclXGens mclXInvs (wordTabS 35 mclXGens
    (mclXWords.getD l.val [])) 5000

end CFSG.Sporadic.SmallOddCore
