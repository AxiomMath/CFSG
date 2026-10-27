module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExc

public section

namespace CFSG.StandardType

open CFSG.Open

@[expose] def GGExcE6NonsplitThreeLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E6 ∧ p = 3 ∧ ¬ 3 ∣ 2 ^ f - 1

@[expose] def GGExcTwE6NonsplitThreeLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .twistedE6 ∧ p = 3 ∧ ¬ 3 ∣ 2 ^ f + 1

@[expose] def GGExcTwE6SplitFiveLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .twistedE6 ∧ p = 5 ∧ 5 ∣ 2 ^ f + 1

end CFSG.StandardType
