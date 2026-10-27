module

public import CFSG.Quasithin.EmptyFaithful.S153G26
public import CFSG.Quasithin.EmptyFaithful.SBc3List

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Input26ComponentBase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    Ctx15325 T Mc M V₁ V₂ Yp I t → Facts15325 T Mc M V₁ V₂ Yp I →
      ∃ L : Subgroup G, L ∈ cComp (thompsonJ I) ∧ ¬ L ≤ M ⊓ I ∧ 1 ≤ CFSG.Open.pRank 3 L ∧
        CFSG.IsQuasisimple ↥(autOn L (UI153 T I))

namespace SBc4

theorem input26Component_of_base (h56 : AsB56) (hB : Input26ComponentBase) : Input26Component := by
  intro G _ _ T Mc M V₁ V₂ Yp I t c hF
  obtain ⟨L, hLc, hLn, hL3, hLq⟩ := hB G T Mc M V₁ V₂ Yp I t c hF
  exact ⟨L, hLc, hLn, hL3, hLq, SBc3.star_mem_list h56 c hF.toFacts153 hLc hLq⟩

end SBc4

end CFSG.Quasithin
