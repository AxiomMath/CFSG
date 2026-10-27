module

public import Certificates.Data.PSp43Sylow
public import Certificates.Data.P43Twin

public section

namespace Certificates.OmegaCentK

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def centL (L : List P45) (t : P45) : List P45 :=
  L.filter fun g => decide (g * t = t * g)

@[expose] def oddL (C : List P45) : List P45 :=
  C.filter fun x => decide (x ^ 9 = 1)

@[expose] def centChk (A0 O : List P45) (t : P45) : Bool :=
  A0.all fun a => !(O.all fun x => decide (a * x = x * a)) || decide (a = 1) || decide (a = t)

@[expose] def check (_ : Unit := ()) : Bool :=
  let t := Certificates.P43Twin.tA ()
  let C := centL (elemsT QP45) t
  centChk (elemsT QA45) (oddL C) t

end Certificates.OmegaCentK
