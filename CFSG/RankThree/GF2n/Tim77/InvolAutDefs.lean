module

public import CFSG.RankThree.GF2n.Tim77Prop24Core

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open Subgroup

@[expose] def Prop24InnerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Ab L Lb M : Subgroup G), Prop24Setup A Ab L Lb M →
    2 < L.relIndex A → ∀ u : G, conjSubgroup u (A ⊔ Ab) = A ⊔ Ab →
    u ∈ centralizer (A : Set G) →
    (∀ x ∈ A ⊔ Ab, (u * u)⁻¹ * x⁻¹ * (u * u) * x ∈ M) →
      ∃ a ∈ A, ∀ x ∈ A ⊔ Ab, (a * u)⁻¹ * x⁻¹ * (a * u) * x ∈ M

end CFSG.RankThree.GF2n.Tim77
