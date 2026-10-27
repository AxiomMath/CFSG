module

public import Certificates.Data.GSThmBCatalog5CovHS
public meta import Certificates.Data.GSThmBCatalog5CovHS

public section

namespace CFSG.ComponentClassification.SolMax.H35.HS

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GSThmB.CovHS

@[expose] def dTab : Tab := hsDGens[0]!

@[expose] def hsH35Check : Bool :=
  comp 3850 dTab dTab == idTab 3850 && !(dTab == idTab 3850) &&
    CFSG.ComponentClassification.J2Cover.fixedCount 3850 (comp 3850 t2Tab dTab) == 30

end CFSG.ComponentClassification.SolMax.H35.HS
