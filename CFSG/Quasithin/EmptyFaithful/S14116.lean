module

public import CFSG.Quasithin.EmptyFaithful.S14115

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_14_1_16 (h113 : StageLemma14113) {T Mc M H : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hTH : T ≤ H) (hHM : H ≤ M)
    (hR : pCoreOf 2 H ≠ ⊥) (hC : cgsIn M (pCoreOf 2 H) = H) : IsUniqueM H M := by
  refine ⟨⟨hM.1, hHM⟩, fun M₁ hM₁ => ?_⟩
  rcases h113 G T Mc h M H hM hTH hHM hR hC.le with ⟨hF, -⟩ | ⟨-, -, hu⟩
  · exact (lemma_14_1_15 h113 h hM).2 M₁
      ⟨hM₁.1, sup_le (hF.trans hM₁.2) (hTH.trans hM₁.2)⟩
  · exact hu.2 M₁ hM₁

end CFSG.Quasithin
