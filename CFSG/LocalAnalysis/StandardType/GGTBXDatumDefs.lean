module

public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGResRows

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBTorLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .A ∨ lab.tag = .twA) ∧ 4 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧
      p ∣ (if lab.tag = .twA then 2 ^ lab.n + 1 else 2 ^ lab.n - 1)) ∨
    ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ p = 3 ∧
      3 ∣ (if lab.tag = .twE6 then 2 ^ lab.n + 1 else 2 ^ lab.n - 1)) ∨
    (lab.tag = .E8 ∧ p = 3)

@[expose] def GGTBWeylRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTBTorLabel p lab ∧ LargeEvenHalfSplit p lab True ∧ ¬ ggRowSeven p lab lab ∧
    lab.tag ≠ .twF4 ∧ lab.tag ≠ .twF4der

end CFSG.StandardType
