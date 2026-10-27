module

public import Certificates.Data.GMS78RuPi7Data
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ComponentClassification.GMS78.RuPi7

open CFSG.CosetTable

abbrev sub3 : List (Fin 7) := subsetOf 7 pi7Sub

abbrev relsP3 : List (List (Fin sub3.length × Bool)) := restrictWords sub3 pi7Rels

abbrev subB : List (Fin sub3.length) := subsetOf sub3.length [0, 1, 2, 3]

abbrev relsB : List (List (Fin subB.length × Bool)) := restrictWords subB relsP3

end CFSG.ComponentClassification.GMS78.RuPi7
