module

public import CFSG.Sporadic.HNOddCore.InvArrays
public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.HNOddCore.OrbitCert
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import CFSG.Sporadic.HNOddCore.OrbitCert
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

@[expose] def g1Words : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [-1, 2], [-1, 3], [10, -11], [-1, 4], [10, -13], [12, -14],
    [-1, 5], [10, -16], [12, -17], [15, -18], [-1, 6], [10, -20], [12, -21], [15, -22], [19, -23],
    [-1, 7], [10, -25], [12, -26], [15, -27], [19, -28], [24, -29], [-1, 8], [10, -31], [12, -32],
    [15, -33], [19, -34], [24, -35], [30, -36]]

@[expose] def g1Sizes : List Nat := [2, 1, 10, 9, 8, 7, 6, 5, 4, 3, 1, 1]

@[expose] def g4Words : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [-7, 8], [-1, 2], [-11, 6, 11], [-6, -12, -11, -1, 9]]

@[expose] def g4Sizes : List Nat := [8, 1, 6, 1, 4, 1, 2, 1, 4, 3, 1, 1]

@[expose] def g6Words : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [], [-1, 2], [-11, 8, 11], [-8, -9, 12, 9, 8], [-9, -10, 13,
    10, 9]]

@[expose] def g6Sizes : List Nat := [12, 10, 8, 1, 1, 6, 1, 4, 1, 1, 1, 1]

@[expose] def g4cWords : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [], [-7, 8], [-1, 2], [-12, 6, 12], [-6, -13, -12, -1, 9],
    [11, -7, -14, -6, -13, -12, -1, 10]]

@[expose] def g4cSizes : List Nat := [8, 1, 6, 1, 4, 1, 2, 1, 4, 3, 2, 1]

@[expose] def tauList : List Nat := [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

@[expose] def base12 : List (Fin 12) := List.finRange 12

@[expose] def natArrs (A : Array (List Nat)) : Array (Array Nat) := A.map List.toArray

@[noinline, expose] def natChainChecks : Bool :=
  chainCheck 12 (natArrs InvData.c1Nat) g1Words base12 g1Sizes &&
    chainCheck 12 (natArrs InvData.c4Nat) g4Words base12 g4Sizes &&
    chainCheck 12 (natArrs InvData.c6Nat) g6Words base12 g6Sizes &&
    chainCheck 12 (natArrs (InvData.c4Nat.push tauList)) g4cWords base12 g4cSizes

@[expose] def bfsList (m : Nat) (gens : Array (Array Nat)) (root : Nat) : Array Nat := Id.run do
  let mut L : Array Nat := #[root]
  let mut seen : Array Bool := (Array.replicate m false).set! root true
  for i in [0:m] do
    if i < L.size then
      for g in gens do
        let y := g[L[i]!]!
        if y < m && !seen[y]! then
          seen := seen.set! y true
          L := L.push y
  return L

@[expose] def orbitOK (m : Nat) (gens : Array (Array Nat)) (L : Array Nat) : Bool :=
  orbitCertOK m gens L (posArr m L) (orbitRecs gens L (posArr m L)).1
    (orbitRecs gens L (posArr m L)).2

@[expose] def s4J : Array (Array Nat) := InvData.s4Perms.extract 0 10

@[noinline, expose] def orbitChecks : Bool :=
  InvData.o1Lists.size == 3 && InvData.o1Lists.map Array.size == #[1, 945, 210] &&
    (allBelowN 3 fun i => orbitOK InvData.f1Arr.size InvData.s1Perms InvData.o1Lists[i]!) &&
    orbitOK InvData.f4Arr.size s4J (bfsList InvData.f4Arr.size s4J 0) &&
    (bfsList InvData.f4Arr.size s4J 0).size == 800 &&
    InvData.o6Lists.size == 2 && InvData.o6Lists.map Array.size == #[7700, 1100] &&
    orbitOK InvData.f6Arr.size InvData.s6Perms InvData.o6Lists[0]! &&
    orbitOK InvData.f6Arr.size InvData.s6Perms InvData.o6Lists[1]!

end CFSG.Sporadic.HNOddCore.Native
