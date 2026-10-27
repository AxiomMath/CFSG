module

public import CFSG.Quasithin.EmptyFaithful.SBc8Cover
public import CFSG.Quasithin.EmptyFaithful.SBc8QY
public import CFSG.Quasithin.EmptyFaithful.SBc7Top

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input31CoverShort : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L → (IsAltBlockType L 6 ∨ IsG2Block L) →
      ∀ d : G, d ∈ I → d ∈ Subgroup.centralizer (Yp : Set G) →
        d ∈ Subgroup.centralizer (blockU L : Set G) → (∃ k : ℕ, d ^ 2 ^ k = 1) →
        ⁅L, Subgroup.zpowers d⁆ ≤ centerOf (blockU L) → d ∈ Subgroup.centralizer (L : Set G)

@[expose] def Input31QleYpShort : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L → (IsAltBlockType L 6 ∨ IsG2Block L) →
      blockU L ≤ Yp

namespace SBc8

theorem input31Cover_of_short (h113 : StageLemma14113) (h : Input31CoverShort) : Input31Cover := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout d hdI hdY hdQ hd2 hcomm
  rcases hout.1 with hA | hG | ⟨-, h1 | h2 | h3⟩
  · exact h G T Mc M V₁ V₂ Yp I L t c hout (Or.inl hA) d hdI hdY hdQ hd2 hcomm
  · exact h G T Mc M V₁ V₂ Yp I L t c hout (Or.inr hG) d hdI hdY hdQ hd2 hcomm
  · exact cover_of_cases123 h113 c hout (Or.inl h1) hdY hdQ hcomm
  · exact cover_of_cases123 h113 c hout (Or.inr (Or.inl h2)) hdY hdQ hcomm
  · exact cover_of_cases123 h113 c hout (Or.inr (Or.inr h3)) hdY hdQ hcomm

theorem input31QleYp_of_short (h113 : StageLemma14113) (h : Input31QleYpShort) : Input31QleYp := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hcase
  rcases hcase with hA | hG | h3
  · exact h G T Mc M V₁ V₂ Yp I L t c hout (Or.inl hA)
  · exact h G T Mc M V₁ V₂ Yp I L t c hout (Or.inr hG)
  · exact blockU_le_Yp_of_case3 h113 c hout h3

theorem input15331_of_short_residues (h113 : StageLemma14113) (hMS : Input31MSOutcome)
    (hC : Input31CoverShort) (hα : Input31QleYpShort) : Input15331 :=
  SBc7.input15331_of_residues hMS (input31Cover_of_short h113 hC) (input31QleYp_of_short h113 hα)

end SBc8

end CFSG.Quasithin
