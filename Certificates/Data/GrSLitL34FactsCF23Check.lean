module

public import Certificates.Data.GrSLitL34FactsRealBCheck

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def sq1M (t i : ℕ) : Bool :=
  comp 42 (comp 42 (wordTab (tg t)) (repTab i)) (comp 42 (wordTab (tg t)) (repTab i)) ==
    idTab 42

@[expose] def invFixM (t i : ℕ) : Bool :=
  allM.any fun x => !(wordTab (tg x.1) == idTab 42) && mulM x x == oneM && betaYM t i x == x

@[noinline, expose] def invFixOK : Bool :=
  (List.range 36).all fun i => (List.range 64).all fun t => !sq1M t i || invFixM t i

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
