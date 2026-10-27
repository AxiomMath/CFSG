module

public import Certificates.Data.SmithL6Orbit

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)

@[expose] def collPtTab : Array Bool := Array.ofFn (n := 512) fun c => uco.contains c.val

@[expose] def collNewPts (j : Nat) : List Nat := uco.toList.filter fun q => 2 ^ j ≤ q && q < 2 ^ (j + 1)

@[expose] def collInSpan (cols : Array Nat) (p : Nat) : Bool :=
  (List.range (2 ^ cols.size)).any fun s => applyCols cols s == p

@[expose] def collGo : Nat → Array Nat → List (Array Nat)
  | 0, cols => [cols]
  | n + 1, cols =>
    let np := collNewPts cols.size
    (uco.toList.filter fun p => np.all (fun q => collPtTab[applyCols (cols.push p) q]!) &&
        !collInSpan cols p).flatMap fun p => collGo n (cols.push p)

@[expose] def collLeaves : List (Array Nat) := collGo 9 #[]

@[expose] def collInvB (cols : Array Nat) : Bool :=
  (List.range 9).all (fun m => applyCols cols cols[m]! == 2 ^ m) &&
    (List.range 9).any fun m => cols[m]! != 2 ^ m

@[expose] def collL : Array (Array Nat) := (collLeaves.filter collInvB).toArray

@[expose] def collMul (A B : Array Nat) : Array Nat := Array.ofFn (n := 9) fun m => applyCols A B[m]!

@[expose] def collComm (A B : Array Nat) : Bool :=
  (List.range 9).all fun m => applyCols A B[m]! == applyCols B A[m]!

@[expose] def collFixTab : Array (Array Bool) :=
  collL.map fun A => Array.ofFn (n := 512) fun v => applyCols A v.val == v.val

@[expose] def collCommTab : Array (Array Bool) := collL.map fun A => collL.map fun B => collComm A B

@[expose] def collFixList : Array (List Nat) :=
  ((List.range collL.size).map fun a => (List.range 512).filter fun v => collFixTab[a]![v]!).toArray

@[expose] def collCommList : Array (List Nat) :=
  ((List.range collL.size).map fun a => (List.range collL.size).filter fun m => collCommTab[a]![m]!).toArray

@[expose] def collFixCount (a : Nat) : Nat := collFixList[a]!.length

@[expose] def collFix3 (a b c : Nat) : Nat :=
  collFixList[a]!.countP fun v => collFixTab[b]![v]! && collFixTab[c]![v]!

@[expose] def collComm3 (a b c : Nat) : Nat :=
  collCommList[a]!.countP fun m => collCommTab[b]![m]! && collCommTab[c]![m]!

@[expose] def chkColl : Bool :=
  (List.range collL.size).all (fun a => collL[a]!.size == 9 && decide (collFixCount a ≤ 64)) &&
  (List.range collL.size).all fun a => collCommList[a]!.all fun b => collCommList[a]!.all fun c =>
    !(collCommTab[b]![c]! && collL[a]! != collL[b]! && collL[c]! != collL[a]! &&
      collL[c]! != collL[b]! && collMul collL[a]! collL[b]! != collL[c]!) ||
        (decide (collFix3 a b c ≤ 16) && decide (collComm3 a b c ≤ 23))

end CFSG.SmithL6
