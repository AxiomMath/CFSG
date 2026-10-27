module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def wordXY (w : List Char) : P45 :=
  w.foldl (fun g c => g * if c = 'x' then x45 else y45) 1

@[expose] def syl1 : P45 := wordXY "yxyyxyxyyyyxyyxyxyyxy".toList

@[expose] def syl2 : P45 := wordXY "xyyxyyxyyyxyyyxyyyxyyyyxyy".toList

@[expose] def syl3 : P45 := wordXY "xyyxyyyxyyyxyyyyxy".toList

@[expose] def QT0 : RawSchreierDatum 45 :=
  certificate (by decide) [tab syl1, tab syl2, tab syl3] [[1, 1, 1, 2, 3]] #v[1, 3] (by decide)

@[expose] def invT0 : List P45 :=
  (elemsT QT0).filter fun g => decide (g * g = 1) && decide (g ≠ 1)

@[expose] def centInvT0 : List P45 :=
  invT0.filter fun g => invT0.all fun t => decide (g * t = t * g)

end CFSG.ComponentClassification.CatFactsSmall.PSp43
