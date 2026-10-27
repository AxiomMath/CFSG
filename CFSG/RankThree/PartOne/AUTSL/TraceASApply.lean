module

public import CFSG.RankThree.PartOne.AUTSL.TraceAS
import all CFSG.RankThree.PartOne.AUTSL.TraceAS

public section

namespace CFSG.RankThree.PartOne.AUTSL

variable {K : Type} [Field K] [CharP K 2]

theorem artinSchreierHom_apply (y : K) : artinSchreierHom (K := K) y = y * y + y := by
  unfold artinSchreierHom
  rfl

end CFSG.RankThree.PartOne.AUTSL

end
