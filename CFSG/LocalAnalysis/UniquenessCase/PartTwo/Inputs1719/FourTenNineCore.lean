module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenQ9

open CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

@[expose] def wordOk (L : List (List Nat)) (target : List Nat) (w : List (List Nat)) : Bool :=
  w.all L.contains && w.foldl cmul cid == target

@[expose] def genCheck (L : List (List Nat)) (words : List (List (List Nat))) : Bool :=
  (List.range 3).all fun j => wordOk L (pslGenC.getD j []) (words.getD j [])

@[expose] def conjL (g gi : List Nat) (E : List (List Nat)) : List (List Nat) :=
  E.map fun e => cmul (cmul g e) gi

@[expose] def centL (T F : List (List Nat)) : List (List Nat) :=
  T.filter fun t => F.all (ccomm t)

structure FTEntry where
  E : List (List Nat)
  g : List Nat
  gi : List Nat
  five : Bool
  K : SubData
  k : List Nat
  ki : List Nat
  e : List Nat
  words : List (List (List Nat))

@[expose] def sThreeCheck (T F : List (List Nat)) (en : FTEntry) : Bool :=
  en.K.ok && en.K.gc.all (fun c => pslLit.contains c || T.contains c) &&
  (centL T F).all en.K.lit.contains &&
  en.K.lit.length == 3 * (en.K.lit.filter T.contains).length &&
  en.K.lit.contains en.k && en.K.lit.contains en.ki && cmul en.k en.ki == cid &&
  F.contains en.e && !((en.K.lit.filter T.contains).contains (cmul (cmul en.k en.e) en.ki))

@[expose] def cFiveCheck (T F : List (List Nat)) (en : FTEntry) : Bool :=
  en.K.ok && en.K.gc == [en.k] && pslLit.contains en.k && en.K.lit.length == 5 &&
  (centL T F).all (normT en.K.lit) && F.contains en.e && !(ccomm en.e en.k)

@[expose] def ftEntryCheck (T : List (List Nat)) (en : FTEntry) : Bool :=
  en.E.all T.contains && pslLit.contains en.g && pslLit.contains en.gi &&
  cmul en.g en.gi == cid && (conjL en.g en.gi en.E).all T.contains &&
  (bif en.five then cFiveCheck T (conjL en.g en.gi en.E) en
    else sThreeCheck T (conjL en.g en.gi en.E) en) &&
  genCheck (en.K.lit ++ T) en.words

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenQ9
