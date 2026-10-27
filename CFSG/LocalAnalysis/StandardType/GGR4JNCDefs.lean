module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTwTorusAutKnown : Prop :=
  ∀ f : ℕ, 1 ≤ f →
    ((3 ∣ 2 ^ f - 1 → LargeEvenLabelAll ⟨.twA, 5, f⟩ fun R _ I _ =>
        GGTorusAutCardSC 3 R I 3 48) ∧
      (3 ∣ 2 ^ f + 1 → LargeEvenLabelAll ⟨.A, 5, f⟩ fun R _ I _ =>
        GGTorusAutCardSC 3 R I 3 48) ∧
      LargeEvenLabelAll ⟨.twD, 4, f⟩ fun R _ I _ => GGTorusAutCardSC 3 R I 3 48)

end CFSG.StandardType

end
