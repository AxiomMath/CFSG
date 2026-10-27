module

public import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def hsCosWords : List (List Nat) :=
  [[], [2, 0, 1, 3, 1, 0], [0], [2], [3], [0, 2], [0, 3], [0, 3, 2]]

@[expose] def hsCosTabs : Array Tab :=
  Array.ofFn (n := 8) fun i => wordTabS 3850 hsC2Tabs (hsCosWords.getD i.val [])

@[expose] def hsCosInvs : Array Tab := hsCosTabs.map (invTab 3850)

@[expose] def hsCosCls : List Nat := [4, 1, 1, 1, 1, 4]

end CFSG.Sporadic.SmallOddCore
