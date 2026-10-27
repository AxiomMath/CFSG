module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldFixD4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ lab.rank = 4 ∧ p = 3 ∧ 2 ≤ lab.n ∧ lab.n ≠ 3

end CFSG.StandardType

end
