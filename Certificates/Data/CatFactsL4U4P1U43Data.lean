module

public import Certificates.Data.CatFactsL4U4P1U43Defs

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def u43Bases : List (Nat × Table × Table) := [
    (0, tu 404334890521881 false, tu 1352341616652227 false),
    (4, tu 1309751274598484 false, tu 1681408017212684 false)]

irreducible_def u43CentTriv : List (Table × Table) := (bfsPairs 820 uPg u43Bases).toList

end CFSG.ComponentClassification.HarrisLit.P1.U43
