module

public import Certificates.Data.Kernel.E6RegPair
public import Certificates.Data.E6DiagRegularLines

public section

namespace CFSG.KC.E6RegInner

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.KC.E6RegPair
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

@[expose] def innerTupleOK (T : RootTables) (t : List ℕ) : Bool :=
  !(e6ScTest e6Certificate r7 t || e6ScTest e6Certificate c0 t) ||
    ((List.range 3).product (List.range 3)).all fun c =>
      (c.1 == 0 && c.2 == 0) ||
        (e6ScTest e6Certificate (combVec c.1 c.2 r7 c0) t ||
          a2FixedL e6Certificate T (killIdx T e6Certificate.roots.length (combVec c.1 c.2 r7 c0)) t)

@[expose] def innerOKWith (T : RootTables) (es : List (ℕ × List ℕ)) : Bool :=
  es.all fun e => innerTupleOK T (tupleOfWord T e.2)

@[expose] def innerOK (es : List (ℕ × List ℕ)) : Bool :=
  innerOKWith (RootTables.ofCert e6Certificate) es

end CFSG.KC.E6RegInner
