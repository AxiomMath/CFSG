module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.SmallF2.Native

@[inline, expose] def cmp11 (C D : Array Nat) : Array Nat := mulRows 11 D C

@[inline, expose] def conjCols (G G' B : Array Nat) : Array Nat := cmp11 (cmp11 G B) G'

abbrev ClsEnum : Type := Array (Array Nat) × Array Nat × Array Nat

@[expose] def clsBFS (gens : Array (Array Nat × Array Nat)) (M : Array Nat) (cap : Nat) :
    ClsEnum := Id.run do
  let mut elts : Array (Array Nat) := #[M]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut idx : Std.HashMap (Array Nat) Nat := (∅ : Std.HashMap (Array Nat) Nat).insert M 0
  for i in [0:cap] do
    if i < elts.size then
      let B := elts[i]!
      for g in [0:gens.size] do
        let C := conjCols gens[g]!.1 gens[g]!.2 B
        if !idx.contains C then
          idx := idx.insert C elts.size
          elts := elts.push C
          par := par.push i
          gen := gen.push g
  return (elts, par, gen)

@[expose] def clsIdx (E : Array (Array Nat)) : Std.HashMap (Array Nat) Nat :=
  Nat.fold E.size (fun i h m => m.insert E[i] i) ∅

@[inline, expose] def colsBounded (C : Array Nat) : Bool :=
  C.size == 11 && (List.range 11).all fun j => C[j]! < 2048

@[expose] def clsOKWith (look : Array Nat → Nat) (gens : Array (Array Nat × Array Nat))
    (M : Array Nat) (n : Nat) (E : ClsEnum) : Bool :=
  E.1[0]! == M &&
    (List.range n).all (fun i => colsBounded E.1[i]! && look E.1[i]! == i) &&
    (List.range n).all (fun i => i == 0 || (E.2.1[i]! < i && E.2.2[i]! < gens.size &&
      E.1[i]! == conjCols gens[E.2.2[i]!]!.1 gens[E.2.2[i]!]!.2 E.1[E.2.1[i]!]!)) &&
    (List.range n).all fun i => (List.range gens.size).all fun g =>
      look (conjCols gens[g]!.1 gens[g]!.2 E.1[i]!) < n &&
        E.1[look (conjCols gens[g]!.1 gens[g]!.2 E.1[i]!)]! ==
          conjCols gens[g]!.1 gens[g]!.2 E.1[i]! &&
        look (conjCols gens[g]!.2 gens[g]!.1 E.1[i]!) < n &&
        E.1[look (conjCols gens[g]!.2 gens[g]!.1 E.1[i]!)]! ==
          conjCols gens[g]!.2 gens[g]!.1 E.1[i]!

@[expose] def clsOK (gens : Array (Array Nat × Array Nat)) (M : Array Nat) (n : Nat)
    (E : ClsEnum) : Bool :=
  let m := clsIdx E.1
  clsOKWith (fun C => m.getD C n) gens M n E

@[expose] def imCols (C : Array Nat) : List Nat :=
  ((List.range 2048).map fun b => b ^^^ vecMulN 11 C b).eraseDups

end CFSG.Quasithin.H13.J4.Native
