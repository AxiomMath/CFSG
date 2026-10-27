module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs

public section

namespace CFSG.StandardType

@[expose] def GGPumpCAutKnownF4 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ, 1 ≤ f → p ∣ (2 ^ f) ^ 2 - 1 →
    LargeEvenLabelAll ⟨.F4, 4, f⟩ fun R _ I _ => GGTorusAutCardSCF4 p f R I 4 1152

end CFSG.StandardType

end
