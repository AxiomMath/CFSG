module

public import CFSG.Sporadic.Schreier.ONCheckAux
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def repWords : Array (List Nat) :=
  #[[0], [1, 1], [2, 1], [3, 3], [4, 3], [5, 3], [5, 4]]

@[expose] def prodArr (n : Nat) (gs : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldr (fun j acc => pcomp n gs[j]! acc) (pid n)

@[expose] def repTabs32 : Array (Array Nat) :=
  repWords.map (prodArr 32 Data.T32Chain.generators)

@[expose] def repOrbits32 : Array CFSG.PSL3Four.Native.Enum :=
  repTabs32.map fun r => CFSG.PSL3Four.Native.orbitBFS 32 Data.T32Chain.generators
    (Data.T32Chain.generators.map (CFSG.PSL3Four.Native.invTab 32)) r 64

@[expose] def vWords : Array (List Int) :=
  #[[-1, -3, -4, -4, 3, 2, -4, -4, 4, 2, 3], [-3, 4, -2, -2, 2, -4, -2],
    [4, 4, 1, 2, 1, -1, -2, 1, -3, -2, -3]]

@[expose] def oddTests : List (Nat × Nat × Nat) :=
  [(0, 0, 15), (1, 1, 15), (2, 2, 19), (4, 2, 19), (5, 0, 19), (6, 2, 15)]

@[expose] def oddArr (tA bA bI : Array (Array Nat)) (z : Array Nat) (i k : Nat) : Array Nat :=
  let v := pword nPts bA bI vWords[k]!
  pcomp nPts (prodArr nPts tA repWords[i]!) (pcomp nPts v (pcomp nPts z (pinvCand nPts v)))

@[noinline, expose] def fusionCheck (tA bA bI : Array (Array Nat)) (z : Array Nat) : Bool :=
  tA.size == 6 && bA.size == 4 && bI.size == 4 &&
    allBelowN 6 (fun j => peq 32 (rTab tA[j]!) Data.T32Chain.generators[j]!) &&
    allBelowN 4 (fun j => pisInv nPts bA[j]! bI[j]!) &&
    peq nPts (prodArr nPts tA repWords[3]!) z &&
    allBelowN 7 (fun i => peq nPts (pcomp nPts (prodArr nPts tA repWords[i]!)
      (prodArr nPts tA repWords[i]!)) (pid nPts) &&
      !peq nPts (prodArr nPts tA repWords[i]!) (pid nPts)) &&
    vWords.all (plettersOK 4) &&
    vWords.all (fun w => pisInv nPts (pword nPts bA bI w) (pinvCand nPts (pword nPts bA bI w))) &&
    oddTests.all fun (i, k, m) =>
      peq nPts (Nat.repeat (pcomp nPts (oddArr tA bA bI z i k)) m (pid nPts)) (pid nPts)

end CFSG.Sporadic.ONOddCore
