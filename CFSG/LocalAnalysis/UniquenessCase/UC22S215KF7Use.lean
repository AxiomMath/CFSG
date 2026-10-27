module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def KF7Use (D : Data G) : Prop :=
  ∀ p ∈ D.sig, ∀ H : Subgroup G, F07.Sec7Hyp D p H →
    IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) ∨
      (p = 5 ∧ ∀ Y : Subgroup (F07.QuotK7 p H),
        Y ≤ ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) →
        ⁅Y, Y⁆ = Y → ∀ (S : Type) [Group S], IsSimpleGroup S →
          ∀ f : ↥Y →* S, Function.Surjective f → IsAlt S 5)

end CFSG.LocalAnalysis.UniquenessCase.UC22
