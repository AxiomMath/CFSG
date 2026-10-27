module

public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native

@[expose] def heXTabs : Array Tab := Array.ofFn (n := 9) fun j => heInnerSigma1.getD j.val #[]

@[expose] def heXInvs : Array Tab := heXTabs.map (invTab 42)

@[expose] def heRWords : List (List Nat) :=
  [[8, 8, 8], [1, 8, 8, 8, 1], [1, 2, 1, 8, 1, 2, 1, 8], [2, 3, 2, 1], [3, 2, 1, 2],
    [8, 3, 8, 2, 1, 8, 1, 8]]

@[expose] def heRGens : Array Tab :=
  Array.ofFn (n := 6) fun j => wordTabS 42 heXTabs (heRWords.getD j.val [])

@[expose] def heXEnum : Enum := enumBFS 42 heXTabs 10752

@[expose] def heREnum : Enum := enumBFS 42 heRGens 64

end CFSG.Sporadic.SmallOddCore
