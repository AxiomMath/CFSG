module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.CFSGNative.He.Certificate
public import CFSG.Certificates.CosetTableCompactColumns
public import Certificates.Data.HePresData
public import CFSG.Certificates.CosetTableShort
public import Mathlib

public section

namespace CFSG.ComponentClassification.AS81.HePres.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.CosetTable

@[expose] def letterArrW {k : Nat} (gens invs : Array (Array Nat)) (l : Fin k × Bool) :
    Array Nat :=
  if l.2 then gens.getD l.1.val #[] else invs.getD l.1.val #[]

@[expose] def wordArrW {k : Nat} (n : Nat) (gens invs : Array (Array Nat))
    (w : List (Fin k × Bool)) : Array Nat :=
  w.foldr (fun l acc => compA n (letterArrW gens invs l) acc) (idA n)

@[expose] def relArrCheck {k : Nat} (n : Nat) (gens invs : Array (Array Nat))
    (rels : List (List (Fin k × Bool))) : Bool :=
  rels.all fun r => eqA n (wordArrW n gens invs r) (idA n)

@[expose] def modelCheck {k : Nat} (n : Nat) (gens : Array (Array Nat))
    (rels : List (List (Fin k × Bool))) : Bool :=
  let invs := gens.map (invCand n)
  (List.range k).all (fun i => isInvA n (gens.getD i #[]) (invs.getD i #[])) &&
    relArrCheck n gens invs rels

@[expose] def toZ {k : Nat} (w : List (Fin k × Bool)) : List Int :=
  w.map fun l => if l.2 then (l.1.val + 1 : Int) else -((l.1.val : Int) + 1)

@[expose] def abTab (α β βi : Table) (l : Int) : Table :=
  if l = 1 ∨ l = -1 then α else if l = 2 then β else βi

@[expose] def genTabs (α β βi : Table) (gw : List (List Int)) : Array Table :=
  (gw.map fun w => wordT 8330 (abTab α β βi) w).toArray

@[expose] def piTab (T Ti : Array Table) (l : Int) : Table :=
  if 0 < l then T[l.toNat - 1]! else Ti[(-l).toNat - 1]!

@[expose] def heT1Letters : List Int := [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2]

@[expose] def heImageCheck (gw : List (List Int)) (rels : List (List (Fin 8 × Bool)))
    (wa wb wz : List (Fin 8 × Bool)) : Bool :=
  let O := CFSG.Sporadic.He.Native.orbitData ()
  let βi := invT 8330 O.beta
  let T := genTabs O.alpha O.beta βi gw
  let Ti := T.map (invT 8330)
  let W := fun w : List (Fin 8 × Bool) => wordT 8330 (piTab T Ti) (toZ w)
  decide (gw.length = 8) && gw.all (lettersOK 2) &&
    (List.range 8).all (fun i => invOK 8330 T[i]! Ti[i]!) &&
    rels.all (fun r => W r == idT 8330) && W wa == O.alpha && W wb == O.beta &&
    W wz == wordT 8330 (abTab O.alpha O.beta βi) heT1Letters

abbrev hePiRelsH₁ := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 6, 7]) hePiRels

abbrev hePiRelsH₂ := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) hePiRelsH₁

abbrev hePiRelsH₃ := restrictWords (subsetOf _ [0, 1, 2, 3]) hePiRelsH₂

end CFSG.ComponentClassification.AS81.HePres.Native
