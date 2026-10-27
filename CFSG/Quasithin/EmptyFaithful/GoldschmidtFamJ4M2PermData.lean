module

public import Certificates.Data.J4M2.Orbit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22DataInputs

public section

namespace CFSG.Quasithin.J4M2

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

@[expose] def iterImg (l : List ℕ) : ℕ → ℕ → ℕ
  | 0, i => i
  | k + 1, i => l.getD (iterImg l k i) 0

@[expose] def cycleOf (l : List ℕ) (i : ℕ) : List ℕ :=
  let len := ((List.range 77).find? fun k => 0 < k && iterImg l k i == i).getD 1
  (List.range len).map fun k => iterImg l k i

@[expose] def cyclesOf (l : List ℕ) : List (List ℕ) :=
  ((List.range 77).foldl (fun (acc : List ℕ × List (List ℕ)) i =>
    if acc.1.contains i || l.getD i 0 == i then acc
    else (acc.1 ++ cycleOf l i, acc.2 ++ [cycleOf l i])) ([], [])).2

@[expose] def permImg (l : List ℕ) : Equiv.Perm (Fin 77) :=
  permOf 77 ((cyclesOf l).map fun c => c.map (Fin.ofNat 77))

@[expose] def sigPerm (n : ℕ) : Equiv.Perm (Fin 77) := permImg (sigData.getD n [])

@[expose] def hexLab : List (List ℕ) := [
    [0, 1, 2, 9, 17, 19], [0, 4, 7, 9, 14, 15], [2, 9, 12, 15, 16, 21],
    [1, 5, 14, 15, 16, 19], [1, 9, 11, 14, 18, 21], [2, 6, 7, 14, 19, 21],
    [0, 2, 10, 14, 16, 18], [7, 8, 12, 15, 17, 19], [0, 8, 9, 12, 18, 20],
    [0, 3, 5, 9, 11, 16], [0, 6, 9, 10, 13, 21], [0, 3, 4, 8, 10, 17],
    [0, 2, 4, 11, 20, 21], [1, 6, 8, 10, 18, 19], [1, 5, 6, 7, 9, 12],
    [1, 2, 6, 11, 13, 16], [4, 9, 11, 12, 13, 17], [10, 11, 16, 17, 19, 21],
    [0, 8, 11, 13, 14, 19], [2, 3, 4, 6, 9, 18], [2, 5, 9, 13, 14, 20],
    [2, 7, 8, 9, 10, 11], [1, 2, 4, 8, 12, 14], [3, 9, 10, 12, 14, 19],
    [5, 8, 10, 12, 13, 16], [1, 3, 4, 7, 11, 19], [1, 12, 13, 19, 20, 21],
    [1, 3, 8, 9, 13, 15], [0, 5, 12, 14, 17, 21], [0, 1, 3, 6, 14, 20],
    [6, 8, 9, 14, 16, 17], [0, 4, 6, 12, 16, 19], [1, 4, 9, 10, 16, 20],
    [1, 3, 12, 16, 17, 18], [1, 2, 7, 15, 18, 20], [0, 3, 15, 18, 19, 21],
    [2, 3, 11, 14, 15, 17], [2, 3, 8, 16, 19, 20], [2, 4, 10, 13, 15, 19],
    [2, 5, 11, 12, 18, 19], [6, 9, 11, 15, 19, 20], [5, 9, 10, 15, 17, 18],
    [2, 4, 5, 7, 16, 17], [6, 12, 13, 14, 15, 18], [0, 2, 5, 6, 8, 15],
    [0, 2, 3, 7, 12, 13], [1, 2, 3, 5, 10, 21], [4, 5, 8, 9, 19, 21],
    [0, 1, 10, 11, 12, 15], [1, 5, 8, 11, 17, 20], [4, 14, 17, 18, 19, 20],
    [3, 5, 6, 13, 17, 19], [3, 5, 7, 8, 14, 18], [0, 6, 7, 11, 17, 18],
    [1, 7, 10, 13, 14, 17], [0, 13, 15, 16, 17, 20], [7, 11, 12, 14, 16, 20],
    [0, 5, 7, 10, 19, 20], [4, 6, 7, 8, 13, 20], [3, 6, 7, 10, 15, 16],
    [2, 8, 13, 17, 18, 21], [1, 4, 6, 15, 17, 21], [5, 6, 16, 18, 20, 21],
    [0, 1, 7, 8, 16, 21], [3, 4, 13, 14, 16, 21], [7, 9, 13, 16, 18, 19],
    [4, 5, 6, 10, 11, 14], [4, 8, 11, 15, 16, 18], [3, 7, 9, 17, 20, 21],
    [0, 1, 4, 5, 13, 18], [3, 4, 5, 12, 15, 20], [8, 10, 14, 15, 20, 21],
    [3, 10, 11, 13, 18, 20], [5, 7, 11, 13, 15, 21], [3, 6, 8, 11, 12, 21],
    [2, 6, 10, 12, 17, 20], [4, 7, 10, 12, 18, 21]]

@[expose] def hexB (i : Fin 77) : Finset (Fin 22) :=
  ((hexLab.getD i.val []).map (Fin.ofNat 22)).toFinset

@[expose] def permutesHex (g : Equiv.Perm (Fin 22)) : Bool :=
  (List.finRange 77).all fun i => (List.finRange 77).any fun j => (hexB i).image g == hexB j

@[expose] def phiRN (g : Equiv.Perm (Fin 22)) : RN 77 :=
  ⟨Vector.ofFn fun i => ((List.finRange 77).find? fun j => hexB j == (hexB i).image g).getD i⟩

@[expose] def blockGens : List (Equiv.Perm (Fin 22)) := mGens ++ tGens ++ lat.flatten

@[expose] def oddPerms : List (Equiv.Perm (Fin 77)) := [sigPerm 12, sigPerm 13, sigPerm 14,
  sigPerm 15, sigPerm 16]

@[expose] def tPerms : List (Equiv.Perm (Fin 77)) :=
  [sigPerm 28, sigPerm 29, sigPerm 30, sigPerm 17]

@[expose] def p0Perms : List (Equiv.Perm (Fin 77)) :=
  (List.range 15).map fun j => sigPerm (17 + j)

@[expose] def wordPhiA : List ℕ := [4, 4, 0, 2, 1, 4, 3]

@[expose] def wordPhiB : List ℕ := [1, 4, 3, 4, 1, 1, 3, 2]

@[expose] def wordsOdd : List (List ℕ) := [
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1,
     0],
    [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,
     0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0,
     1]]

@[expose] def i5Fin : List (Fin 77) := i5List.map (Fin.ofNat 77)

@[expose] def fix0 (x : RN 77) : Bool := x.val[0] == 0

@[expose] def presI5 (x : RN 77) : Bool := i5Fin.all fun i => i5Fin.contains x.val[i]

@[expose] def chkSig : Bool :=
  (List.range 32).all fun n => (List.range 77).all fun i =>
    ((sigPerm n) (Fin.ofNat 77 i)).val == (sigData.getD n []).getD i 0

@[expose] def chkHex : Bool :=
  hexLab.length == 77 && hexLab.all (fun h => h.length == 6 && h.all (· < 22)) &&
    (List.finRange 77).all (fun i =>
      (List.finRange 77).all fun j => i == j || hexB i != hexB j) &&
    blockGens.all permutesHex

@[expose] def chkWords : Bool :=
  let phiA := phiRN (mGens.getD 0 1)
  let phiB := phiRN (mGens.getD 1 1)
  phiA != 1 && phiA == evalW (oddPerms.map RN.enc) wordPhiA &&
    phiB == evalW (oddPerms.map RN.enc) wordPhiB &&
    (List.range 5).all fun k =>
      RN.enc (oddPerms.getD k 1) == evalW [phiA, phiB] (wordsOdd.getD k [])

@[expose] def chkT : Bool :=
  closedH (tPerms.map RN.enc) (elts RN.enc 64 tPerms) && (elts RN.enc 64 tPerms).size == 256 &&
    p0Perms.all (fun g => (elts RN.enc 64 tPerms).contains (RN.enc g)) &&
    tGens.all fun g => (elts RN.enc 64 tPerms).contains (phiRN g)

@[expose] def members : List (List (Equiv.Perm (Fin 22))) := tGens :: lat

@[expose] def chkClass : Bool :=
  (List.range 6).all (fun j => j == 4 ||
    (members.getD j []).all (fun g => fix0 (phiRN g)) ||
      (members.getD j []).all fun g => presI5 (phiRN g)) &&
    p0Perms.all fun g => fix0 (RN.enc g) && presI5 (RN.enc g)

end CFSG.Quasithin.J4M2
