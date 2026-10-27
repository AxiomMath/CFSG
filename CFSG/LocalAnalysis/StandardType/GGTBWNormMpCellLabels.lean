module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTBWNormW3SplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ p = 3 ∧ 3 ∣ lab.rank + 1 ∧ 12 ≤ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTBWNormW3UnitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ p = 3 ∧ 3 ∣ lab.rank + 1 ∧ 12 ≤ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGTBWNormW4SplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 5 ≤ p ∧ lab.rank + 1 = 4 * p ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTBWNormW5SplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 5 ≤ p ∧ p ∣ lab.rank + 1 ∧ 5 * p ≤ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTBWNormW5UnitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 5 ≤ p ∧ p ∣ lab.rank + 1 ∧ 5 * p ≤ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1

end CFSG.StandardType

end
