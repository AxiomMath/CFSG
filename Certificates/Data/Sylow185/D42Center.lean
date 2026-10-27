module

public import Certificates.Data.HuppertD4Q2.Checker

public section

namespace HuppertD4Q2

open CFSG.AGLEmbedding.ChevOuter

@[expose] def centralP (_ : Unit := ()) : List Pr :=
  let gens := sGenP ()
  (sElems ()).filter fun z => gens.all fun g => commP z g

@[expose] def centerCheck (_ : Unit := ()) : Bool :=
  let C := centralP ()
  sylowCheck () && decide (C.length = 3) && C.all fun z => z.2 == 0

end HuppertD4Q2
