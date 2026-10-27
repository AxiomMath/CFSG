
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum

@[expose] def odd3 : List (Equiv.Perm (Fin 8)) :=
  (elemsV QA8).filter fun x => decide (x ^ 3 = 1) && !decide (x = 1)

@[expose] def noNilpLen : Nat := 5040

@[expose] def noNilpBlock (j : Nat) : Bool :=
  noNilpCheck (((elemsV QS8).drop (j * noNilpLen)).take noNilpLen) odd3 315

end CFSG.Certificates.Kernel.CatFacts
