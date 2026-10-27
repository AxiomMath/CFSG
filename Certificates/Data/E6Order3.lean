module

public import Certificates.Data.E6DiagRegular

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

@[expose] def imgN (k i : ℕ) : ℕ := e6Certificate.table.getD k 0 / 256 ^ i % 256

@[expose] def reflIdx : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | n + 1, b, c =>
    if b < 6 then imgN c b else
      imgN (reflIdx n (e6Certificate.parent b) (imgN c (e6Certificate.parentReflection b)))
        (e6Certificate.parentReflection b)

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3
