module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.SuzLm

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native

@[expose] def lmNineOK (_ : Unit := ()) : Bool :=
  let T := matEnum.tabs
  let e := idTab 64
  anyBelow T.size fun k =>
    let s := T[k]!
    let s3 := comp 64 s (comp 64 s s)
    !(s3 == e) && comp 64 s3 (comp 64 s3 s3) == e

@[expose] def lmStabOK (_ : Unit := ()) : Bool :=
  let T := matEnum.tabs
  allBelow 63 fun x => (T.toList.filter fun t => t[x + 1]! == x + 1).length % 27 != 0

@[expose] def lmCentOK (_ : Unit := ()) : Bool :=
  let T := matEnum.tabs
  let e := idTab 64
  allBelow T.size fun k =>
    let s := T[k]!
    !(comp 64 s s == e) || s == e ||
      (T.toList.filter fun t => comp 64 t s == comp 64 s t).length % 27 != 0

@[expose] def lmRankOK (_ : Unit := ()) : Bool := lmNineOK () && lmStabOK () && lmCentOK ()

end CFSG.LocalAnalysis.GLTheoremA.H1017.SuzLm
