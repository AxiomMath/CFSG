module

public import Certificates.Data.GrSLitL34FactsCF23Check
public import Certificates.Data.GrSLitL34FactsCF23HeCheck

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def eqC2 (x y : MElt) : Bool :=
  x.1 == y.1 && (x.2.1 - y.2.1).val % 2 == 0 && (x.2.2 - y.2.2).val % 2 == 0

@[expose] def hjTau : MElt := (0, 0, 1)

@[expose] def hjGood : List MElt :=
  hjLabels.map fun l => (l.1, (l.2.1 : ZMod 4), (l.2.2.1 : ZMod 4))

@[expose] def hjFixM (t i : ℕ) : Bool :=
  hjGood.any fun x => !(wordTab (tg x.1) == idTab 42) && eqC2 (mulM x x) oneM &&
    eqC2 (betaYM t i x) x

@[noinline, expose] def hjFixOK : Bool :=
  (List.range 36).all fun i => (List.range 64).all fun t =>
    !sq1M t i || !eqC2 (betaYM t i hjTau) hjTau || hjFixM t i

end CFSG.ComponentClassification.GSThmB.CF23L34
