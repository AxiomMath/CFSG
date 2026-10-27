module

public import CFSG.Sporadic.SuzRecog.LocalRFusionTests
public meta import CFSG.Sporadic.SuzRecog.LocalRFusionTests

public section

namespace CFSG.Sporadic.SuzRecog.LocalR

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.SuzRecog

@[expose] def orbGens : Array Tab := #[cTab 2, cTab 4]

@[expose] def orbInvs : Array Tab := orbGens.map (invTab 1782)

@[expose] def orbWord (w : List Nat) : Tab := w.foldr (fun k t => comp 1782 orbGens[k]! t) (idTab 1782)

@[expose] def cBackWords : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [0],
    [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0],
    [1],
    [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]]

@[expose] def lambdaOrbit2 (i : Nat) : Enum :=
  orbitBFS 1782 orbGens orbInvs (lambdaTab i) lambdaSizes[i]!

@[expose] def lambdaOrbitTabs2 : Array (Array Tab) :=
  Array.ofFn (n := 4) fun i => (lambdaOrbit2 i.val).tabs

@[expose] def s1Idx : List Nat := [0, 8, 10, 12]

@[expose] def s1Gens : Array Tab := Array.ofFn (n := 4) fun j => sylowGenTab (s1Idx.getD j.val 0)

@[expose] def s1Enum : Enum := enumBFS 1782 s1Gens 8192

@[expose] def s1V0 : Array Tab := centTabs 1782 s1Enum.tabs (lambdaTab 3)

@[expose] def genCheck : Bool :=
  allBelow 10 fun k => (cBackWords.getD k []).all (· < 2) && orbWord (cBackWords.getD k []) == cTab k

@[expose] def orbits2Check : Bool :=
  allBelow 4 fun i =>
    orbitOK 1782 orbGens orbInvs (lambdaTab i) (lambdaOrbit2 i) &&
      (lambdaOrbit2 i).tabs.size == lambdaSizes[i]!

@[expose] def sylow2Check : Bool :=
  enumOK 1782 s1Gens s1Enum && s1Enum.tabs.size == 8192 &&
    coverOK 1782 s1Enum.tabs lambdaOrbitTabs2

@[expose] def v02Check : Bool :=
  s1V0.size == 512 &&
    (allBelow 512 fun j => pow4Tab s1V0[j]! == idTab 1782 || pow4Tab s1V0[j]! == tTab) &&
    anyBelow 512 fun j => pow4Tab s1V0[j]! == tTab

end CFSG.Sporadic.SuzRecog.LocalR
