module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def conjA (n : Nat) (g x : Array Nat) : Array Nat :=
  compA n g (compA n x (invCand n g))

@[expose] def treeConj (n : Nat) (g₀ g₁ s₀ : Array Nat) (tree : Array Nat) : Array (Array Nat) :=
  tree.foldl (fun acc t => acc.push (conjA n (if t % 2 = 0 then g₀ else g₁) acc[t / 2]!)) #[s₀]

@[expose] def fi24KBase : Array Nat := #[0, 1, 2, 3, 4, 7, 6]

@[expose] def fi24PBase : Array Nat := #[0, 1, 2, 5]

@[noinline, expose] def fi24KChainOK (S : Array (Array Nat)) (W : Array (List Int)) : Bool :=
  S.size == 12 && rawChainOK 504 (S.extract 0 2) S fi24KBase W 4 &&
    (rawOrbitSizes 504 S fi24KBase).prod == 80263249920

@[noinline, expose] def fi24PChainOK (P : Array (Array Nat)) (W : Array (List Int)) : Bool :=
  P.size == 10 && rawChainOK 378 (P.extract 0 2) P fi24PBase W 4 &&
    (rawOrbitSizes 378 P fi24PBase).prod == 19595520

@[noinline, expose] def fi24SOK (S : Array (Array Nat)) (s₀ tree : Array Nat)
    (P : Array (Array Nat)) : Bool :=
  let T := treeConj 504 S[0]! S[1]! s₀ tree
  let lv := rawLevels 504 S fi24KBase
  T.size == 378 &&
    allLt 378 (fun j => isInvA 504 T[j]! (invCand 504 T[j]!) &&
      siftA 504 lv fi24KBase 0 T[j]! &&
      eqA 504 (conjA 504 S[0]! T[j]!) T[P[0]![j]!]! &&
      eqA 504 (conjA 504 S[1]! T[j]!) T[P[1]![j]!]!) &&
    allLt 378 (fun j => allLt 378 fun k => j == k || !(eqA 504 T[j]! T[k]!)) &&
    allLt 378 (fun j => allLt 378 fun k =>
      eqA 504 (compA 504 T[j]! T[k]!) (compA 504 T[k]! T[j]!))

end CFSG.Sporadic.FischerOddCore
