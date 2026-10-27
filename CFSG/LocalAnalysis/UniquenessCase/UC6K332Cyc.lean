module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

@[expose] def K332Cyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ → CFSG.Open.pRank 3 S ≤ 3 →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = 3 → IsWeaklyClosedIn Z S →
    ∀ (Q : Type) [Group Q], IsCyclic Q → ∀ φ : ↥S →* Q, Disjoint (Z.subgroupOf S) φ.ker →
    CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1

end CFSG.LocalAnalysis.UniquenessCase.UCK
