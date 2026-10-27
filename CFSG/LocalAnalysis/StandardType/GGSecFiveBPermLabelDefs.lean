module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveBPermLinLabel (n p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ lab.rank = n - 1 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGSecFiveBPermUniLabel (n p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = n - 1 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGSecFiveBPermLabel (n p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGSecFiveBPermLinLabel n p lab ∨ GGSecFiveBPermUniLabel n p lab

end CFSG.StandardType

end
