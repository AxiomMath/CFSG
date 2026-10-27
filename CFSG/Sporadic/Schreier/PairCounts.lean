module

public import Certificates.Data.CFSGNative.PairSchreier.Counts

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Schreier.PairNative

theorem countOrd_eq (bs : List Nat) (m : Nat) (Bs : List (Array (Array Nat))) :
    countOrd bs m Bs = countW (ordPred bs m) Bs [] :=
  rfl

theorem countPair_eq (bs : List Nat) (my : Nat) (x : List (Array Nat))
    (conds : List (List Bool × Nat)) (Bs : List (Array (Array Nat))) :
    countPair bs my x conds Bs = countW (pairPred bs my x conds) Bs [] :=
  rfl

end CFSG.Sporadic.Schreier
