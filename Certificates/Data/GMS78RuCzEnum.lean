module

public import Certificates.Data.GMS78RuCzPres
public import Certificates.Data.GMS78RuCzGammaData
public import Certificates.Data.GMS78RuAsmData
public import Certificates.Data.GMS78RuPi7RuData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open CFSG.CosetTable CFSG.Sporadic.Bridge.SurjD.Native CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native

abbrev sub9 : List (Fin 10) := subsetOf 10 [0, 1, 2, 3, 4, 5, 6, 7, 8]

abbrev p12Rels : List (List (Fin sub9.length × Bool)) := restrictWords sub9 czRels

@[expose] def natWord (w : List ℕ) : List (ℕ × Bool) := w.map fun c => (c / 2, c % 2 == 0)

@[expose] def invNatWord (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def l10Word (i : ℕ) : List (ℕ × Bool) := natWord (czL10Codes.getD i [])

@[expose] def substWord (r : List (ℕ × Bool)) : List (ℕ × Bool) :=
  r.flatMap fun l => if l.2 then l10Word l.1 else invNatWord (l10Word l.1)

@[expose] def czRuRels : List (List (ℕ × Bool)) :=
  czRels.map (fun r => substWord (r.map fun l => (l.1.val, l.2))) ++
    (List.range 6).map fun i => (i, false) :: substWord (natWord (czL6Codes.getD i []))

@[expose] def m2Letter (k : ℕ) : ℕ := [0, 1, 2, 3, 4, 6].getD k 0

@[expose] def m2Word (w : List ℕ) : List (ℕ × Bool) := w.map fun c => (m2Letter (c / 2), c % 2 == 0)

@[expose] def gWord (p : ℕ) : List (ℕ × Bool) :=
  m2Word (c2ImgCodes.getD (if p < 5 then p else if p = 6 then 5 else 6) [])

@[expose] def gSubst (r : List (ℕ × Bool)) : List (ℕ × Bool) :=
  r.flatMap fun l => if l.2 then gWord l.1 else invNatWord (gWord l.1)

@[expose] def c2RuRels : List (List (ℕ × Bool)) :=
  ((pi7Rels.filter fun r => (renumber (subsetOf 7 [0, 1, 2, 3, 4, 6]) r).isSome).map fun r =>
      gSubst (r.map fun l => (l.1.val, l.2))) ++
    ((List.range 6).map fun k => (m2Letter k, false) :: gSubst (m2Word (c2InvCodes.getD k []))) ++
    (RuAsm.ruA0Words.map fun a =>
      invNatWord (a.map fun l => (l.1.val, l.2)) ++ gSubst (a.map fun l => (l.1.val, l.2))) ++
    [invNatWord (l10Word 6) ++ gSubst (l10Word 6)] ++
    ((List.range 4).map fun i => invNatWord (natWord (c2BCodes.getD i [])) ++ gWord i) ++
    ((List.range 9).map fun y =>
      invNatWord (substWord (natWord (c2TrivCodes.getD y [])) ++ l10Word y) ++
        gSubst (l10Word y)) ++
    ((List.range 6).map fun i =>
      invNatWord (substWord (natWord (c2JCodes.getD i []))) ++ gSubst (l10Word i))

end CFSG.ComponentClassification.GMS78.RuCz
