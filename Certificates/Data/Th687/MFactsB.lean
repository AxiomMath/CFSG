module

public import CFSG.Sporadic.Th.Max3.Relations
public import CFSG.Sporadic.Th.Recog.JLettersInputs
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Recognition.PresentedWordsClosure
public import CFSG.Sporadic.Th.Max3.CentA

public section

namespace CFSG.Sporadic.Th.Recog.MFactsBData

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def rowsT (_ : Unit := ()) : Array V4 := wordRows rowsX rowsY (wJ 6)

@[expose] def commFilter (G : Array V4) : List (Fin 512) :=
  (List.finRange 512).filter fun k =>
    eqRows (mulRows G (rowsNfAt k)) (mulRows (rowsNfAt k) G)

@[expose] def centTList (_ : Unit := ()) : List (Fin 512) :=
  let T := rowsT ()
  commFilter T

@[expose] def centTCenter (_ : Unit := ()) : Bool :=
  let C := centTList ()
  C.all fun k =>
    if k.val = 0 ∨ k.val = 1 then true
    else C.any fun k' =>
      eqRows (mulRows (rowsNfAt k) (rowsNfAt k'))
        (mulRows (rowsNfAt k') (rowsNfAt k)) == false

end CFSG.Sporadic.Th.Recog.MFactsBData
