module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTBRowR3 (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank

@[expose] def GGTBRowR4 (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4

@[expose] def GGTBRowR5 (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∨ lab.tag = .twD) ∧ 3 ≤ lab.rank

@[expose] def GGTBRowR6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ≠ 3

end CFSG.StandardType

end
