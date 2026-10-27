module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockResC
public import CFSG.Quasithin.EmptyFaithful.R3c20C
public import CFSG.Quasithin.EmptyFaithful.S151S4E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Input15120L2BlockN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListA15120 L →
    IsBlock2 (L ⊔ s1516 T Z₁) L ∧ (L ∈ cComp (g1_1516 Z₁) → Case15120TwoA T Mc Z₁ L)

theorem input15120L2BlockN_of_res_l2 (h118 : TheoremC118) (h126 : TheoremC126)
    (h116 : R3c20.TheoremC116L2) (hLJ : Input15120LJ) (h1416 : StageLemma1416)
    (h15 : StageLemma1515CE) (hwr : Input15120WreathChar) (hres : Input15120L2BlockResC) :
    Input15120L2BlockN := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hA
  obtain ⟨n, hn, hLn⟩ := hA
  by_cases hblock : IsBlock2 (L ⊔ s1516 T Z₁) L
  · refine ⟨hblock, fun hLc => ?_⟩
    obtain ⟨hb, hg⟩ := hres G T Mc M Z₁ Z₂ V₁ V₂ L hc hLc hchar ⟨n, hn, hLn⟩ hblock
    exact ⟨hblock, hb, hg⟩
  · exfalso
    have hq := hc.ctx.qtfe
    have hLM : ¬ L ≤ M :=
      lemma_15_1_20_one (h1416 G T Mc hq).1 hc.ctx.mf (h15 G T Mc M hq hc.ctx.mf hc.ctx.ce) hc.hL
    have hbaum : baum (s1516 T Z₁) ≤ Subgroup.normalizer (L : Set G) := by
      by_cases hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G)
      · exact (C1GN.baum_le _).trans hSN
      · exact R3c20.baum_le_normalizer_of_l2 (h116 G) hc hchar hn hLn
          (hwr G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar ⟨n, hn, hLn⟩ hblock hSN) hSN
          (hLJ G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar)
    exact hblock (S151S4.l2_isBlock_of_baum h118 h126 hc hLM hchar hn hLn hbaum)

end CFSG.Quasithin
