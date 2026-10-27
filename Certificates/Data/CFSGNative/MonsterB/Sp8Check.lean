module

public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model

public section

namespace CFSG.Monster.B.Rep4371.Native.Sp8

open CFSG.Monster.B.Rep4371.Native

@[expose] def rowChain : List (Bool → Nat → Bool × Bool × Nat) → Bool → Nat → Bool × Bool × Nat
  | [], η, c => (false, η, c)
  | f :: fs, η, c =>
    let r := f η c
    let r' := rowChain fs r.2.1 r.2.2
    (r.1 ^^ r'.1, r'.2.1, r'.2.2)

@[expose] def rowChainEq (fs gs : List (Bool → Nat → Bool × Bool × Nat)) : Bool :=
  (List.range 4096).all fun c => [false, true].all fun η => rowChain fs η c == rowChain gs η c

@[expose] def noAKeys (v : List (Key × Int)) : Bool := v.all fun e => e.1.1 != 0

@[expose] def xiKeyRow (q : Pauli) (η : Bool) (c : Nat) : Bool :=
  let v : List (Key × Int) := [(Key.W η c, 1)]
  let l := actVec (keyActSign 3) v
  let r₁ := actVec keyActXi v
  let r₂ := actVec (keyActPauli q) r₁
  noAKeys l && noAKeys r₂ && eqModel 4096 (actVec keyActXi l) 262144 (actVec (keyActSign 3) r₂)

@[expose] def xiKeyCheck (q : Pauli) : Bool :=
  (List.range 4096).all fun c => [false, true].all fun η => xiKeyRow q η c

end CFSG.Monster.B.Rep4371.Native.Sp8
