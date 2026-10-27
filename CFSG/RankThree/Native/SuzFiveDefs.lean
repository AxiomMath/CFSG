module

public import CFSG.RankThree.Native.SuzFiveData
public import CFSG.RankThree.Native.PermEnumeration

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def suzFiveQArrs : Array (Array Nat) := suzFiveSylowIdx.map suzFiveArr

@[expose] def suzFiveLineArr (i : Nat) : Array Nat := suzFiveArr suzFiveLineIdx[i]!

@[expose] def suzFiveCArrs (i : Nat) : Array (Array Nat) := suzFiveCentIdx[i]!.map suzFiveArr

@[expose] def suzFiveQ : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (permsA 1782 suzFiveQArrs)

@[expose] def suzFiveLine (i : Fin 6) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (suzFiveLineArr i)

@[expose] def suzFiveC (i : Fin 6) : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (permsA 1782 (suzFiveCArrs i))

@[expose] def suzFiveD (i : Fin 6) : Subgroup (Equiv.Perm (Fin 1782)) := ⁅suzFiveC i, suzFiveC i⁆

@[expose] def suzFiveGen (i : Fin 6) (j : Nat) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (suzFiveCArrs i)[j]!

@[expose] def suzFiveMults (i : Nat) : Array (Array Nat) :=
  (suzFiveCArrs i ++ (suzFiveCArrs i).map (invCand 1782)).foldl
    (fun acc g => if acc.contains g then acc else acc.push g) #[]

abbrev SuzFiveBfsState := Array (Array Nat) × Std.HashMap Nat (List Nat)

@[expose] def suzFiveKey (p : Array Nat) : Nat := keyA 1782 (List.range 8) p

@[expose] def suzFiveSeen (st : SuzFiveBfsState) (p : Array Nat) : Bool :=
  (st.2.getD (suzFiveKey p) []).any fun k => eqA 1782 st.1[k]! p

@[expose] def suzFiveAdd (st : SuzFiveBfsState) (p : Array Nat) : SuzFiveBfsState :=
  (st.1.push p, st.2.insert (suzFiveKey p) (st.1.size :: st.2.getD (suzFiveKey p) []))

@[expose] def suzFiveVisit (ms : Array (Array Nat)) (st : SuzFiveBfsState) (c : Array Nat) :
    SuzFiveBfsState :=
  ms.foldl (fun st m =>
    let p := compA 1782 m c
    if suzFiveSeen st p then st else suzFiveAdd st p) st

@[expose] def suzFiveBfsLoop (ms : Array (Array Nat)) : Nat → Nat → SuzFiveBfsState →
    SuzFiveBfsState
  | 0, _, st => st
  | fuel + 1, pos, st =>
    if h : pos < st.1.size then suzFiveBfsLoop ms fuel (pos + 1) (suzFiveVisit ms st st.1[pos])
    else st

@[expose] def suzFiveBfs (i : Nat) : Array (Array Nat) :=
  (suzFiveBfsLoop (suzFiveMults i) (Nat.factorial 1782) 0 (suzFiveAdd (#[], ∅) (idA 1782))).1

@[expose] def suzFiveEnum (i : Fin 6) (k : Nat) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (suzFiveBfs i)[k]!

@[expose] def suzFiveDArrs (i : Nat) : Array (Array Nat) :=
  let E := suzFiveBfs i
  suzFiveDerivedPairs[i]!.map fun p => commutatorA 1782 (suzFiveCArrs i)[p.1]! E[p.2]!

@[expose] def suzFiveDerivedGen (i : Fin 6) (l : Nat) : Equiv.Perm (Fin 1782) :=
  let p := (suzFiveDerivedPairs[i.val]!)[l]!
  suzFiveGen i p.1 * suzFiveEnum i p.2 * (suzFiveGen i p.1)⁻¹ * (suzFiveEnum i p.2)⁻¹

end CFSG.RankThree.Native
