module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBNbrInnerRound12ExcRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n + 1) ∨
  (lab.tag = .E6 ∧ ((p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.n = 1 ∧ (p = 3 ∨ p = 7)))) ∨
  (lab.tag = .twE6 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) ∨
  (lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n + 1) ∨
  ((lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1) ∧ lab.rank = 5 ∧
    p = 3)

@[expose] def GGTableBNbrInnerRound12ExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound12Label p lab ∧ GGTableBNbrInnerRound12ExcRow p lab

end CFSG.StandardType
