module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTableBNbrInnerNineClassicalLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (((lab.tag = .A ∧ 2 ≤ lab.rank) ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧
      ∀ j, 0 < j → 3 * j ≤ (if lab.tag = .D then 4 else lab.rank + 1) →
        ¬ p ∣ (2 ^ lab.n) ^ j - 1) ∨
    (((lab.tag = .twA ∧ 2 ≤ lab.rank) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
      ∀ j, 0 < j → 3 * j ≤ (if lab.tag = .twD then 4 else lab.rank + 1) →
        ¬ p ∣ ((2 ^ lab.n) ^ 2) ^ j - 1) ∨
    ((lab.tag = .B ∨ lab.tag = .C) ∧
      ∀ j, 0 < j → 3 * j ≤ 2 * lab.rank → ¬ p ∣ (2 ^ lab.n) ^ j - 1) ∨
    ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧
      ∀ j, 0 < j → 3 * j ≤ 2 * lab.rank → ¬ p ∣ (2 ^ lab.n) ^ j - 1)

end CFSG.StandardType
