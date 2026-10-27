module

public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueInputs

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Recognition.McLMultiplier

@[expose] def genZ (i : Fin 6) : List ℤ :=
  if i.val = 0 then [1] else if i.val = 1 then [2]
  else if i.val = 2 then Ly0.decodeWord "dcddcDDCD"
  else if i.val = 3 then Ly0.decodeWord "ddcdcDCDD"
  else if i.val = 4 then Ly0.decodeWord "dcdcddcDDCDCD" else []

@[expose] def genTabsB : Array Table :=
  Array.ofFn (n := 6) fun i => Ly0.wT Ly0.tabs0 Ly0.invs0 (genZ i)

@[expose] def genInvTabsB : Array Table :=
  Array.ofFn (n := 6) fun i => Ly0.wT Ly0.tabs0 Ly0.invs0 (invW (genZ i))

@[expose] def letterTabB (l : Fin 6 × Bool) : Table :=
  if l.2 then genTabsB[l.1.val]! else genInvTabsB[l.1.val]!

@[expose] def wordTabB (w : List (Fin 6 × Bool)) : Table :=
  w.foldr (fun l acc => compT Ly0.deg (letterTabB l) acc) (idT Ly0.deg)

@[expose] def isBWord (w : List (Fin 6 × Bool)) : Bool := w.all fun l => decide (l.1.val < 5)

@[expose] def bWordCheck (r : List (Fin 6 × Bool)) : Bool :=
  isBWord r && tblEq Ly0.deg (wordTabB r) (idT Ly0.deg)

@[expose] def kLetter : Fin 6 × Bool := (5, true)

@[expose] def kkRel : List (Fin 6 × Bool) := [kLetter, kLetter]

@[expose] def eRel (U V : List (Fin 6 × Bool)) : List (Fin 6 × Bool) :=
  kLetter :: (U ++ kLetter :: V)

abbrev EEv := List ℤ × List (Fin 6 × Bool) × List (Fin 6 × Bool)

@[expose] def substW (Ut : List ℤ) : List ℤ :=
  Ut.flatMap fun (l : ℤ) =>
    if 0 < l then Ly1080.erelWords[(l - 1).toNat]! else invW Ly1080.erelWords[(-l - 1).toNat]!

@[expose] def isUWord (w : List ℤ) : Bool := w.all fun l => l != 0 && decide (l.natAbs ≤ 4)

@[expose] def eCheck (ev : EEv) : Bool :=
  isUWord ev.1 && isBWord ev.2.1 && isBWord ev.2.2 &&
    tblEq Ly0.deg (wordTabB ev.2.1) (wordT Ly0.deg Glue.uLetB ev.1) &&
    tblEq Ly0.deg (compT Ly0.deg (wordT Ly0.deg Glue.uLetB (substW ev.1)) (wordTabB ev.2.2))
      (idT Ly0.deg)

@[expose] def eRelOf (ev : EEv) : List (Fin 6 × Bool) := eRel ev.2.1 ev.2.2

@[expose] def zOf (l : Fin 5 × Bool) : ℤ := if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def tOfInts (l : List ℤ) : List (Fin 5 × Bool) :=
  l.map fun z => (Fin.ofNat 5 (z.natAbs - 1), decide (0 < z))

abbrev TrSeg := List (Fin 6 × Bool) × List (Fin 5 × Bool)

abbrev TrEv := TrSeg × List TrSeg

@[expose] def trRel (ev : TrEv) : List (Fin 6 × Bool) :=
  ev.1.1 ++ ev.2.flatMap fun sg => kLetter :: sg.1

@[expose] def trWord (ev : TrEv) : List (Fin 5 × Bool) :=
  ev.1.2 ++ ev.2.flatMap fun sg => ((4 : Fin 5), true) :: sg.2

@[expose] def isTxWord (t : List (Fin 5 × Bool)) : Bool := t.all fun l => decide (l.1.val < 4)

@[expose] def txWordTab (t : List (Fin 5 × Bool)) : Table :=
  t.foldr (fun l acc => compT Ly0.deg (Glue.txLetB (zOf l)) acc) (idT Ly0.deg)

@[expose] def trWordTab (t : List (Fin 5 × Bool)) : Table :=
  t.foldr (fun l acc => compT Ly243.deg (Ly243.trLet (zOf l)) acc) (idT Ly243.deg)

@[expose] def segCheck (sg : TrSeg) : Bool :=
  isBWord sg.1 && isTxWord sg.2 && tblEq Ly0.deg (wordTabB sg.1) (txWordTab sg.2)

@[expose] def trCheck (ev : TrEv) : Bool :=
  segCheck ev.1 && ev.2.all segCheck &&
    tblEq Ly243.deg (trWordTab (trWord ev)) (idT Ly243.deg)

@[expose] def famCheck (eEvs : List EEv) (trEvs : List TrEv) (R : List (List (Fin 6 × Bool))) :
    Bool :=
  R.all fun r => bWordCheck r || r == kkRel || eEvs.any (fun e => r == eRelOf e && eCheck e) ||
    trEvs.any (fun ev => r == trRel ev && trCheck ev)

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
