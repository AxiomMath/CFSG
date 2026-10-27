module

public import Certificates.Data.E6DiagRegular
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
meta import Certificates.Data.E6DiagRegular
meta import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6ShapeKernel

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

@[expose] def independent (a b : List ℕ) : Bool :=
  a != List.replicate 6 0 && b != List.replicate 6 0 && b != a &&
    b != a.map (fun x => 2 * x % 3)

@[expose] def kernelCount (T : RootTables) (a b : List ℕ) : ℕ :=
  let aa := castL a
  let bb := castL b
  ((List.range T.vecs.length).filter fun k =>
    decide (pairZ T k aa % 3 = 0) && decide (pairZ T k bb % 3 = 0)).length

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6ShapeKernel
