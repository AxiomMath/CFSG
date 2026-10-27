module

public import Certificates.Data.GMS78RuAsmAlign
public import Certificates.Data.GMS78RuNModel
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7 CFSG.GMS78RuN

abbrev ruSub2 : List (Fin 7) := subsetOf 7 [0, 1, 2, 3, 4, 6]

abbrev ruRels2 : List (List (Fin ruSub2.length × Bool)) := restrictWords ruSub2 pi7Rels

abbrev ruSub2B : List (Fin ruSub2.length) := subsetOf ruSub2.length [0, 1, 2, 3]

abbrev ruRels2B : List (List (Fin ruSub2B.length × Bool)) := restrictWords ruSub2B ruRels2

@[expose] def ruNACheckModel : Bool :=
  pi7Rels.all fun r => (renumber ruSub2 r).isNone || nEvalW r == nOneT

end CFSG.ComponentClassification.GMS78.RuAsm
