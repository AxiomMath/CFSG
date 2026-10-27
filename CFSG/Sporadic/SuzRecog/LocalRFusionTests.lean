module

public import CFSG.Sporadic.SuzRecog.TwistTests
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public meta import CFSG.Sporadic.SuzRecog.TwistTests
public meta import CFSG.Sporadic.SuzOddCore.InvTCheckInputs

public section

namespace CFSG.Sporadic.SuzRecog.LocalR

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog

@[expose] def fusionGens : Array Tab := Array.ofFn (n := 10) fun k => cTab k.val

@[expose] def fusionInvs : Array Tab := fusionGens.map (invTab 1782)

@[expose] def lambda3Word : List Nat := [1]

@[expose] def lambda4Word : List Nat := [4, 9, 4, 7, 3]

@[expose] def lambdaTab (i : Nat) : Tab :=
  if i = 0 then tTab else if i = 1 then qProds[1]! else
    if i = 2 then cWord lambda3Word else cWord lambda4Word

@[expose] def lambdaSizes : Array Nat := #[1, 54, 360, 6480]

@[expose] def lambdaFixed : Array Nat := #[54, 54, 54, 42]

@[expose] def lambdaOrbit (i : Nat) : Enum :=
  orbitBFS 1782 fusionGens fusionInvs (lambdaTab i) lambdaSizes[i]!

@[expose] def lambdaOrbitTabs : Array (Array Tab) :=
  Array.ofFn (n := 4) fun i => (lambdaOrbit i.val).tabs

@[expose] def sylowLiftWords : List (List Nat) :=
  [[1], [6], [3, 5, 3], [7, 9, 2, 4], [3, 2, 1, 9, 8], [3, 6, 5, 7]]

@[expose] def sylowGenTab (j : Nat) : Tab :=
  if j < 6 then qArr j else if j = 6 then tTab else cWord (sylowLiftWords.getD (j - 7) [])

@[expose] def fusionSylowGens : Array Tab := Array.ofFn (n := 13) fun j => sylowGenTab j.val

@[expose] def fusionSylowEnum : Enum := enumBFS 1782 fusionSylowGens 8192

@[expose] def fusionV0 : Array Tab := centTabs 1782 fusionSylowEnum.tabs (lambdaTab 3)

@[expose] def pow4Tab (t : Tab) : Tab := comp 1782 (comp 1782 t t) (comp 1782 t t)

@[expose] def sizesCheck : Bool :=
  (allBelow 10 fun k => (cTab k).size == 1782) &&
    (allBelow 4 fun i => (lambdaTab i).size == 1782) &&
    (allBelow 13 fun j => (sylowGenTab j).size == 1782) &&
    (qProds[4]!).size == 1782 && (qProds[8]!).size == 1782

@[expose] def orbitsCheck : Bool :=
  allBelow 4 fun i =>
    orbitOK 1782 fusionGens fusionInvs (lambdaTab i) (lambdaOrbit i) &&
      (lambdaOrbit i).tabs.size == lambdaSizes[i]!

@[expose] def sylowCheck : Bool :=
  enumOK 1782 fusionSylowGens fusionSylowEnum && fusionSylowEnum.tabs.size == 8192 &&
    coverOK 1782 fusionSylowEnum.tabs lambdaOrbitTabs

@[expose] def v0Check : Bool :=
  fusionV0.size == 512 &&
    (allBelow 512 fun j => pow4Tab fusionV0[j]! == idTab 1782 || pow4Tab fusionV0[j]! == tTab) &&
    anyBelow 512 fun j => pow4Tab fusionV0[j]! == tTab

@[expose] def repsCheck : Bool :=
  (allBelow 4 fun i =>
    comp 1782 (lambdaTab i) (lambdaTab i) == idTab 1782 && !(lambdaTab i == idTab 1782) &&
      fixedCount (lambdaTab i) == lambdaFixed[i]!) &&
    comp 1782 qProds[4]! qProds[4]! == idTab 1782 &&
    comp 1782 qProds[8]! qProds[8]! == idTab 1782 &&
    comp 1782 qProds[4]! (lambdaTab 1) == comp 1782 (lambdaTab 1) qProds[4]! &&
    comp 1782 qProds[8]! (lambdaTab 1) == comp 1782 (lambdaTab 1) qProds[8]! &&
    comp 1782 (comp 1782 (comp 1782 qProds[4]! qProds[8]!) qProds[4]!) qProds[8]! == tTab

@[expose] def fusionCheck : Bool :=
  sizesCheck && orbitsCheck && sylowCheck && v0Check && repsCheck

end CFSG.Sporadic.SuzRecog.LocalR
