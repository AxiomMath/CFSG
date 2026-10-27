module

public import Certificates.Data.SmithL6Coll
public import Std.Data.HashMap

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)

set_option compiler.extract_closed false

@[expose] def trIdT : Array Nat := Array.ofFn (n := 1953) fun x => x.val

@[expose] def trCompT (s t : Array Nat) : Array Nat :=
  Array.ofFn (n := 1953) fun x => s[t[x.val]!]!

@[expose] def trTvT (p : Nat) : Array Nat := tvTab[p]!

@[expose] def trSw (x : Nat) : Nat := ((x &&& 7) <<< 3) ||| (x >>> 3)

@[expose] def trTauT : Array Nat :=
  Array.ofFn (n := 1953) fun k =>
    tvIdxTab[64 * trSw (tvPair k.val).2 + trSw (tvPair k.val).1]!

@[expose] def trLift : Nat → Array Nat
  | 0 => trIdT
  | 1 => trTvT 0
  | 2 => trTvT 224
  | 3 => trCompT (trTvT 0) (trTvT 224)
  | _ => trTauT

@[expose] def trGens : Array Nat := #[1216, 1, 720, 93, 157, 1720]

@[expose] def trColsT (s : Array Nat) : Array Nat :=
  Array.ofFn (n := 9) fun j => uco[pos0 s[ugens[j.val]!]!]!

@[expose] def trConjC (g M : Array Nat) : Array Nat := collMul (collMul g M) g

@[expose] def trRootMats (_ : Unit) : List (Array Nat) :=
  (List.range 4).map fun j => trColsT (trLift (j + 1))

@[expose] def trXorSel : List Nat → Nat → Nat
  | [], _ => 0
  | b :: bs, m => (if m % 2 = 1 then b else 0) ^^^ trXorSel bs (m / 2)

@[expose] def trCandT (s : Array Nat) (a : Nat) : Array Nat :=
  Array.ofFn (n := 1953) fun x => uaWord a s[x.val]!

@[expose] def trFixL (c : Array Nat) : List Nat := (List.range 1953).filter fun x => c[x]! == x

end CFSG.SmithL6
