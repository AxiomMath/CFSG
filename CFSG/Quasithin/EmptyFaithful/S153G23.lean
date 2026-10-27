module

public import CFSG.Quasithin.EmptyFaithful.S153GExtra
public import CFSG.Quasithin.EmptyFaithful.S153D15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L3Branch1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅VZ T M, YL153 Yp L⁆ = ⊥ → False

@[expose] def L3Branch2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L → Concl15314Two T Mc M →
      ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥ →
      (IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
        Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) → False

@[expose] def L3Closing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥ → Yp = Y153 Mc M →
        ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 W ∧ L ≤ Subgroup.normalizer (W : Set G) ∧
          T ≤ Subgroup.normalizer (W : Set G) ∧ Y153 Mc M ≤ Subgroup.normalizer (W : Set G)

theorem input15323_of_narrow (h113 : StageLemma14113) (h12 : Input15312TwoL3) (h14 : Input15314Two)
    (h1 : L3Branch1) (h2 : L3Branch2) (h3 : L3Closing) : Input15323 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq
  have c12 := h12 G T Mc M V₁ V₂ Yp I L t c hq
  by_cases hV : ⁅VZ T M, YL153 Yp L⁆ = ⊥
  · exact h1 G T Mc M V₁ V₂ Yp I L t c hq c12 hV
  · have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.toCtx15313L.ctx.hyp
    rcases hh.cases with hYY | hU
    · obtain ⟨W, hW0, hW2, hWL, hWT, hWY⟩ := h3 G T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY
      have hLc : L ∈ cComp (thompsonJ I) := c.toCtx15313L.conc.1
      have hLn : ¬ L ≤ M ⊓ I := c.toCtx15313L.conc.2.1
      have hLle : L ≤ I := le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ hLc)
      have hCO : W ≤ pCoreOf 2 (Subgroup.normalizer (W : Set G)) :=
        le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hW2
      have hXN : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (W : Set G) := sup_le hWY hWT
      have hH : InH (Y153 Mc M ⊔ T) (Subgroup.normalizer (W : Set G)) :=
        ⟨hXN, fun hb => hW0 (le_bot_iff.mp (hb ▸ hCO))⟩
      have hNM : Subgroup.normalizer (W : Set G) ≤ M :=
        le_of_isUniqueM (Hyp153.lemma_15_3_7_unique h113 hh.hyp) hH
      exact hLn (le_inf (hWL.trans hNM) hLle)
    · exact h2 G T Mc M V₁ V₂ Yp I L t c hq c12
        (h14 G T Mc M V₁ V₂ Yp I t c.toCtx15313L.ctx hU) hV hU

end CFSG.Quasithin
