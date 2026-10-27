module

public import Certificates.Data.SmithB45MatQ

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H.Mathieu

@[expose] def inM22s2 (s : T22s2.Elem) : Bool :=
  (T22s2.arr s)[0]! == 0

@[expose] def predQ22in (l : List T22s2.Elem) : Bool :=
  !(l.all inM22s2) || predQ 10 actC22s2 true l

end CFSG.Quasithin.B45Mat
