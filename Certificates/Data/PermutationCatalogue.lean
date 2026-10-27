module

public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Certificates.PermutationCatalogue.Data

open CFSG.PSL3Four.Native

structure Transition where
  representative : Nat
  conjugator : Nat
  target : Nat
  words : Array (Array (Option Nat))
deriving Inhabited

structure Cover where
  transition : Nat
  left : Nat
  right : Nat
deriving Inhabited

structure Row where
  gens : Array Nat
  elems : Enum
  transitions : Array Transition
  cover : Array Cover
deriving Inhabited

structure Input where
  ambient : Enum
  ambientInv : Array Tab
  rows : Array Row
  bottom : Nat
deriving Inhabited

@[expose] def rowGens (ambient : Enum) (P : Row) : Array Tab :=
  Array.ofFn (n := P.gens.size) fun k => ambient.tabs[P.gens[k.val]]!

@[expose] def gensBounded (ambient : Array Tab) (gens : Array Nat) : Bool :=
  allBelow gens.size fun k => gens[k]! < ambient.size

@[expose] def wordBounded (k : Nat) (w : Array (Option Nat)) : Bool :=
  allBelow w.size fun i =>
    match w[i]! with
    | none => true
    | some j => j < k

@[expose] def wordTab (n : Nat) (gs : Array Tab) (r : Tab) : List (Option Nat) → Tab
  | [] => idTab n
  | none :: w => comp n r (wordTab n gs r w)
  | some k :: w => comp n gs[k]! (wordTab n gs r w)

@[expose] def rowIndexes (I : Input) : Array (Std.HashMap Tab Nat) :=
  Array.ofFn (n := I.rows.size) fun i => indexOf (I.rows[i.val]!).elems.tabs

@[expose] def transitionOKWithIndex (n : Nat) (ambient : Enum) (ambientInv : Array Tab)
    (rows : Array Row) (idxT : Std.HashMap Tab Nat) (i : Nat) (t : Transition) : Bool :=
  i < rows.size &&
    t.representative < ambient.tabs.size &&
    t.conjugator < ambient.tabs.size &&
    t.target < rows.size &&
    (let src := rows[i]!
     let tgt := rows[t.target]!
     let gs := rowGens ambient src
     let ts := rowGens ambient tgt
     gensBounded ambient.tabs src.gens &&
       gensBounded ambient.tabs tgt.gens &&
       (let c := ambient.tabs[t.conjugator]!
        let ci := ambientInv[t.conjugator]!
        let r := ambient.tabs[t.representative]!
        allBelow gs.size (fun k => found idxT tgt.elems.tabs (conjTab n ci c gs[k]!)) &&
          found idxT tgt.elems.tabs (conjTab n ci c r) &&
          t.words.size == ts.size &&
          allBelow ts.size (fun k =>
            wordBounded gs.size t.words[k]! &&
              (wordTab n gs r (t.words[k]!).toList == conjTab n c ci ts[k]!))))

@[expose] def transitionOK (n : Nat) (ambient : Enum) (ambientInv : Array Tab)
    (rows : Array Row) (i : Nat) (t : Transition) : Bool :=
  transitionOKWithIndex n ambient ambientInv rows
    (indexOf (rows[t.target]!).elems.tabs) i t

@[expose] def coverOK (n : Nat) (ambient : Enum) (rows : Array Row) (i : Nat) : Bool :=
  i < rows.size &&
    (let src := rows[i]!
     src.cover.size == ambient.tabs.size &&
       allBelow ambient.tabs.size fun h =>
         let cv := src.cover[h]!
         cv.transition < src.transitions.size &&
           (let t := src.transitions[cv.transition]!
            t.representative < ambient.tabs.size &&
              cv.left < src.elems.tabs.size &&
              cv.right < src.elems.tabs.size &&
              (comp n (comp n src.elems.tabs[cv.left]! ambient.tabs[t.representative]!)
                  src.elems.tabs[cv.right]! == ambient.tabs[h]!)))

@[expose] def rowsBounded (I : Input) : Bool :=
  allBelow I.rows.size fun i => gensBounded I.ambient.tabs (I.rows[i]!).gens

@[expose] def rowsEnumOK (n : Nat) (I : Input) : Bool :=
  allBelow I.rows.size fun i =>
    enumOK n (rowGens I.ambient (I.rows[i]!)) (I.rows[i]!).elems

@[expose] def rowsTransitionsOK (n : Nat) (I : Input) : Bool :=
  let idxs := rowIndexes I
  allBelow I.rows.size fun i =>
    let src := I.rows[i]!
    allBelow src.transitions.size fun k =>
      let t := src.transitions[k]!
      t.target < I.rows.size &&
        transitionOKWithIndex n I.ambient I.ambientInv I.rows (idxs[t.target]!) i t

@[expose] def rowsCoverOK (n : Nat) (I : Input) : Bool :=
  allBelow I.rows.size fun i => coverOK n I.ambient I.rows i

@[expose] def bottomOK (I : Input) : Bool :=
  I.bottom < I.rows.size && (I.rows[I.bottom]!).gens.size == 0

@[expose] def ambientInvsOK (n : Nat) (I : Input) : Bool :=
  invsOK n I.ambient.tabs I.ambientInv

@[expose] def catalogueOK (n : Nat) (I : Input) : Bool :=
  ambientInvsOK n I && rowsBounded I && rowsEnumOK n I &&
    rowsTransitionsOK n I && rowsCoverOK n I && bottomOK I

end CFSG.Certificates.PermutationCatalogue.Data
