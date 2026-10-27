module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ANe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeYb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeRoute1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeRoute2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23ne_ns_of_nonsplit {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_2 D V₀ V hV L) (h0 : V₀ ≠ ⊥) {x : G}
    {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hbad : ¬ (c23neY V K₁ K₂ = V₀ ∨ C23NeSplit V₀ V (c23neY V K₁ K₂) (K₁ ⊔ K₂))) :
    C23NeNs D V₀ V L hV x K₁ K₂ := by
  have h151 := hS.setting.hyp151
  have hP := h151.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hsmall : mSub V₀ ≤ 2 := hS.setting.hyp16.small
  have hV0 : InCalV0 D.M V₀ V := by
    rcases h151.hyp125.1 with ⟨-, hbot⟩ | h2
    · exact absurd hbot h0
    · exact h2.1
  exact
  { ctx := hctx
    pf := hP
    nat := exists_natQuot3 (c23ne_binaryNatural D.M hV h0 hc.2.1)
    small := hsmall
    Y_ne_bot := c23ne_Y_ne_bot hctx hMs hP.le hsmall hV0
    Y_ne := fun h' => hbad (Or.inl h')
    nonsplit := fun h' => hbad (Or.inr h') }

theorem c23Gap64Ne_of (D : Data G) (h119 : F11.R119 D) (h126 : R126 D) : C23Gap64Ne D := by
  intro hSg hx h61 h127 h129 h1217 _ h145 h63 V₀ V L hV hS hc h154 h0 hne
  obtain ⟨x, K₁, K₂, hctx⟩ := c23ne_ctx_of_case D h119 h127 h1217 hS hc h0
  by_cases hgood : c23neY V K₁ K₂ = V₀ ∨ C23NeSplit V₀ V (c23neY V K₁ K₂) (K₁ ⊔ K₂)
  · exact c23ne_false_of_good D hSg hx h61 h127 h129 h1217 h145 h63 hS hc h154 hctx hgood
  · exact c23ne_false_of_ns D h126 h63 hS hc h154 hne (c23ne_ns_of_nonsplit hS hc h0 hctx hgood)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
