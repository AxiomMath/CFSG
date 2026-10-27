module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveWeakNbr {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)) (K : Subgroup G) : Prop :=
  (∃ y : G, GGNbr p B x D J y K) ∧ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦

theorem GGSecFiveWeakNbr.of_mem {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {K : Subgroup G} (hK : K ∈ 𝒦) : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K :=
  ⟨hcfg.2.2.2.1.2 K hK, le_sup_of_le_right (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) K hK)⟩

end CFSG.StandardType

end
