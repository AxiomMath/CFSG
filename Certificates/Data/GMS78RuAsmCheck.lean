module

public import Certificates.Data.GMS78RuPi7RuData

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.GMS78.RuPi7

@[expose] def ruAsmNatWord (w : List (Fin 7 × Bool)) : List (Nat × Bool) :=
  w.map fun l => (l.1.val, l.2)

@[expose] def ruAsmInvWord (w : List (Fin 7 × Bool)) : List (Fin 7 × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

end CFSG.ComponentClassification.GMS78.RuAsm
