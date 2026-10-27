module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis

@[expose] def FirstTransferData {G : Type*} [Group G] (S N : Subgroup G) (x : G) : Prop :=
  (∃ P : Sylow 2 G, (P : Subgroup G) = S) ∧ N ≤ S ∧
    ∃ _ : (N.subgroupOf S).Normal, IsMulCommutative (S ⧸ N.subgroupOf S) ∧
      ∃ hx : x ∈ S, x ∉ N ∧ orderOf x = 2 ∧
        ∀ (g : G) (hg : g⁻¹ * x * g ∈ S),
          (QuotientGroup.mk' (N.subgroupOf S) ⟨g⁻¹ * x * g, hg⟩ : S ⧸ N.subgroupOf S) =
            QuotientGroup.mk' (N.subgroupOf S) ⟨x, hx⟩

end CFSG.LocalAnalysis
