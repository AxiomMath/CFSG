module

public import CFSG.Quasithin.EmptyFaithful.SBc8Top
public import CFSG.Quasithin.EmptyFaithful.SBc9Gen
public import CFSG.Quasithin.EmptyFaithful.SBc9A6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input31CoverG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L → IsG2Block L →
      ∀ d : G, d ∈ I → d ∈ Subgroup.centralizer (Yp : Set G) →
        d ∈ Subgroup.centralizer (blockU L : Set G) → (∃ k : ℕ, d ^ 2 ^ k = 1) →
        ⁅L, Subgroup.zpowers d⁆ ≤ centerOf (blockU L) → d ∈ Subgroup.centralizer (L : Set G)

@[expose] def Input31QleYpG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L → IsG2Block L → blockU L ≤ Yp

@[expose] def Input31G2NoFixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L → IsG2Block L →
      ∀ q ∈ blockU L, q ∈ Subgroup.centralizer (Yp : Set G) → q ∈ blockZ L

@[expose] def Input31G2Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L → IsG2Block L →
      ∀ q ∈ blockU L, ∃ r ∈ ⁅blockU L, Yp⁆, r⁻¹ * q ∈ blockZ L

namespace SBc9

theorem cover_of_alt6 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (h113 : StageLemma14113) (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hAlt : IsAltBlockType L 6)
    {d : G} (hdY : d ∈ Subgroup.centralizer (Yp : Set G))
    (hdQ : d ∈ Subgroup.centralizer (blockU L : Set G))
    (hcomm : ⁅L, Subgroup.zpowers d⁆ ≤ centerOf (blockU L)) :
    d ∈ Subgroup.centralizer (L : Set G) :=
  cover_of_centralizer_le c hAlt.1 (alt6_centralizer_le_blockZ h113 c.toCtx15330 hAlt) hdY hdQ hcomm

theorem blockU_le_Yp_of_alt6 {G : Type} [Group G] [Finite G]
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hAlt : IsAltBlockType L 6) : blockU L ≤ Yp :=
  blockU_le_Yp_of_cover c hAlt.1 (alt6_blockU_cover h113 c.toCtx15330 hAlt)

theorem input31CoverG2_of_noFixed (h : Input31G2NoFixed) : Input31CoverG2 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hG d _ hdY hdQ _ hcomm
  exact cover_of_centralizer_le c hG.1 (h G T Mc M V₁ V₂ Yp I L t c hout hG) hdY hdQ hcomm

theorem input31QleYpG2_of_cover (h : Input31G2Cover) : Input31QleYpG2 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hG
  exact blockU_le_Yp_of_cover c hG.1 (h G T Mc M V₁ V₂ Yp I L t c hout hG)

theorem input31CoverShort_of_g2 (h113 : StageLemma14113) (h : Input31CoverG2) : Input31CoverShort := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hcase d hdI hdY hdQ hd2 hcomm
  rcases hcase with hA | hG
  · exact cover_of_alt6 h113 c hA hdY hdQ hcomm
  · exact h G T Mc M V₁ V₂ Yp I L t c hout hG d hdI hdY hdQ hd2 hcomm

theorem input31QleYpShort_of_g2 (h113 : StageLemma14113) (h : Input31QleYpG2) :
    Input31QleYpShort := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hcase
  rcases hcase with hA | hG
  · exact blockU_le_Yp_of_alt6 h113 c hA
  · exact h G T Mc M V₁ V₂ Yp I L t c hout hG

theorem input15331_of_g2_residues (h113 : StageLemma14113) (hMS : Input31MSOutcome)
    (hC : Input31CoverG2) (hα : Input31QleYpG2) : Input15331 :=
  SBc8.input15331_of_short_residues h113 hMS (input31CoverShort_of_g2 h113 hC)
    (input31QleYpShort_of_g2 h113 hα)

theorem input15331_of_g2_module_facts (h113 : StageLemma14113) (hMS : Input31MSOutcome)
    (hC : Input31G2NoFixed) (hα : Input31G2Cover) : Input15331 :=
  input15331_of_g2_residues h113 hMS (input31CoverG2_of_noFixed hC) (input31QleYpG2_of_cover hα)

end SBc9

end CFSG.Quasithin
