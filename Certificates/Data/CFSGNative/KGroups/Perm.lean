module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.KGroups.Native

open CFSG.Monster.B.Co2.Native

@[expose] def powA (n : Nat) (a : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | k + 1 => compA n a (powA n a k)

@[expose] def orderIsA (n : Nat) (a : Array Nat) (m : Nat) : Bool :=
  eqA n (powA n a m) (idA n) &&
    (List.range m).all fun k => k == 0 || !eqA n (powA n a k) (idA n)

@[expose] def evalWA (n : Nat) (a b : Array Nat) : List Bool → Array Nat
  | [] => idA n
  | false :: w => compA n a (evalWA n a b w)
  | true :: w => compA n b (evalWA n a b w)

@[expose] def pairInvA (n : Nat) (ws : List (List Bool × Nat)) (a b : Array Nat) : Bool :=
  ws.all fun wk => orderIsA n (evalWA n a b wk.1) wk.2

@[expose] def countPairsA (n : Nat) (ws : List (List Bool × Nat)) (L1 L2 : List (Array Nat)) :
    Nat :=
  (L1.map fun a => (L2.filter fun b => pairInvA n ws a b).length).sum

@[expose] def centTrivA (n : Nat) (L : List (Array Nat)) (a b : Array Nat) : Bool :=
  L.all fun s => !(eqA n (compA n s a) (compA n a s) && eqA n (compA n s b) (compA n b s)) ||
    eqA n s (idA n)

@[expose] def isInvolA (n : Nat) (t : Array Nat) : Bool :=
  eqA n (compA n t t) (idA n) && !eqA n t (idA n)

@[expose] def centLenA (n : Nat) (LP : List (Array Nat)) (t : Array Nat) : Nat :=
  (LP.filter fun g => eqA n (compA n g t) (compA n t g)).length

@[expose] def centInA (n : Nat) (LA LS : List (Array Nat)) : Bool :=
  LA.all fun s =>
    !(LS.all fun q => eqA n (compA n s q) (compA n q s)) || LS.any fun q => eqA n s q

end CFSG.KGroups.Native
