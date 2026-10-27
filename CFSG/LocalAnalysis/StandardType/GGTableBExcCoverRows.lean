module

public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGCoverRkCoprimeNarrow17Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TBExcInnRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGL48TBExcTwoRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3

@[expose] def GGL48TBE6Row (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGL48TBTwE6Row (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1

end CFSG.StandardType
