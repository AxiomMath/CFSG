module

public section

namespace CFSG.Monster.B.Binary.Native

@[expose] def insertVec (T : Array Nat) : Nat → Nat → Option (Array Nat)
  | 0, _ => none
  | fuel + 1, v =>
    if v = 0 then some T
    else
      let p := Nat.log2 v
      let t := T[p]?.getD 0
      if t = 0 then some (T.set! p v) else insertVec T fuel (v ^^^ t)

@[expose] def elimList (d : Nat) : Array Nat → List Nat → Option (Array Nat)
  | T, [] => some T
  | T, v :: vs =>
    match insertVec T (d + 1) v with
    | none => none
    | some T' => elimList d T' vs

@[expose] def elimTable (d : Nat) (vs : List Nat) : Option (Array Nat) :=
  elimList d (Array.replicate d 0) vs

@[expose] def tableRank (d : Nat) (T : Array Nat) : Nat :=
  ((List.range d).map fun p => if T[p]! = 0 then 0 else 1).sum

end CFSG.Monster.B.Binary.Native
