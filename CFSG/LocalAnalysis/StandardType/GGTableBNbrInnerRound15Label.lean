module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBNbrInnerRound15ExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound14ExcLabel p lab ∧
    ¬ (lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)

end CFSG.StandardType

end
