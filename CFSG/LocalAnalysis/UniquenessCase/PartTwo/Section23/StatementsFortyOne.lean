module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFortyOneFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L.S2341Frame

@[expose] def NoOddInverted {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) : Prop :=
  ∀ x : Bar2 D.M, x ≠ 1 → Odd (orderOf x) → ∀ v w : D.M, (v : G) ∈ X.W → (w : G) ∈ X.W →
    (w : G) ∉ X.Zh → (QuotientGroup.mk v : Bar2 D.M) * x * (QuotientGroup.mk v)⁻¹ = x⁻¹ →
      Commute (QuotientGroup.mk w : Bar2 D.M) x → False

end Ctx23L.S2341Frame

end CFSG.LocalAnalysis.UniquenessCase.UC22
