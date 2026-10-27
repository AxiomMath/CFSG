module

public import Certificates.Data.CFSGNative.Th.Base

public section

namespace CFSG.Sporadic.Bridge.Th

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def imgText : String := include_str "ThImages.txt"

@[expose] def stdText : String := include_str "ThStd.txt"

@[expose] def hexVal (c : Char) : UInt64 :=
  if c.toNat < 58 then (c.toNat - 48).toUInt64 else (c.toNat - 87).toUInt64

@[expose] def hexWord (cs : Array Char) (start len : Nat) : UInt64 :=
  (List.range len).foldl
    (fun w k => w ||| (hexVal (cs[start + k]?.getD '0') <<< UInt64.ofNat (4 * k))) 0

@[expose] def hexRow (s : String) : V4 :=
  let cs := s.toList.toArray
  ⟨hexWord cs 0 16, hexWord cs 16 16, hexWord cs 32 16, hexWord cs 48 14⟩

@[expose] def parseMats (s : String) : Array (Array V4) :=
  let rows := (((s.splitOn "\n").filter fun l => !l.isEmpty).map hexRow).toArray
  (List.range (rows.size / 248)).toArray.map fun k => rows.extract (248 * k) (248 * k + 248)

@[expose] def letterOfInt (z : Int) : Nat × Bool :=
  if 0 < z then ((z - 1).toNat, true) else ((-z - 1).toNat, false)

@[expose] def parseWord (s : String) : List (Nat × Bool) :=
  ((s.splitOn " ").filterMap String.toInt?).map letterOfInt

@[expose] def parseWords (s : String) : List (List (Nat × Bool)) :=
  ((s.splitOn "\n").filter fun l => !l.isEmpty).map parseWord

@[expose] def imgMats : Array (Array V4) := parseMats imgText

@[expose] def stdWords : List (List (Nat × Bool)) := parseWords stdText

@[expose] def letterRows (mats invs : Array (Array V4)) (l : Nat × Bool) : Array V4 :=
  if l.2 then mats[l.1]?.getD idRows else invs[l.1]?.getD idRows

@[expose] def wordRows (mats invs : Array (Array V4)) (w : List (Nat × Bool)) : Array V4 :=
  w.foldl (fun acc l => mulRows acc (letterRows mats invs l)) idRows

@[expose] def invsOK (mats invs : Array (Array V4)) : Bool :=
  mats.size == invs.size && (List.range mats.size).all fun k =>
    eqRows (mulRows (mats[k]?.getD idRows) (invs[k]?.getD idRows)) idRows

@[noinline, expose] def imageChecks (rels : List (List (Nat × Bool))) (I Iv : Array (Array V4)) :
    Bool :=
  I.size == 8 && invsOK I Iv && rels.all (fun r => eqRows (wordRows I Iv r) idRows) &&
    eqRows (wordRows I Iv (stdWords[0]?.getD [])) (rowsOf seedA) &&
    eqRows (wordRows I Iv (stdWords[1]?.getD [])) (rowsOf seedB)

@[noinline, expose] def inverseChecks (rels : List (List (Nat × Bool))) (I : Array (Array V4)) :
    Bool :=
  imageChecks rels I (I.map invRows)

@[expose] def thCheck (rels : List (List (Nat × Bool))) : Bool :=
  inverseChecks rels imgMats

end CFSG.Sporadic.Bridge.Th
