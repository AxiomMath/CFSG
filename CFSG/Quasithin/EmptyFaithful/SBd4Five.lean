module

public import CFSG.Quasithin.EmptyFaithful.S153G24
public import CFSG.Quasithin.EmptyFaithful.S153D50

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L5Parabolics : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → IsLnTwoQuot L 5 →
      ∃ X₁ X₂ : Subgroup G, Yp ⊔ Sgp153 T V₁ ≤ X₁ ∧ Yp ⊔ Sgp153 T V₁ ≤ X₂ ∧ X₁ ≤ I ∧ X₂ ≤ I ∧
        X₁ ≠ I ∧ X₂ ≠ I ∧ L ≤ X₁ ⊔ X₂

@[expose] def L4FiveMin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316Min T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → IsLnTwoQuot L 5 → False

namespace SBd4

theorem l4FiveMin_of_parabolics (kP : L5Parabolics) : L4FiveMin := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c17 hq
  obtain ⟨X₁, X₂, h₁, h₂, hX₁I, hX₂I, hne₁, hne₂, hLX⟩ :=
    kP G T Mc M V₁ V₂ Yp I L t c.toCtx15316 c17 hq
  have hX₁M : X₁ ≤ M := S153D.le_M_of_minCE c.ctx c.facts c.minimal hX₁I h₁ hne₁
  have hX₂M : X₂ ≤ M := S153D.le_M_of_minCE c.ctx c.facts c.minimal hX₂I h₂ hne₂
  have hLc : L ∈ cComp (thompsonJ I) := c.conc.1
  have hLn : ¬ L ≤ M ⊓ I := c.conc.2.1
  have hLle : L ≤ I := le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ hLc)
  exact hLn (le_inf (hLX.trans (sup_le hX₁M hX₂M)) hLle)

theorem input15324M_of_narrow (h113 : StageLemma14113) (h4 : L4Four) (h5 : L4FiveMin) :
    Input15324M := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hc
  refine ⟨fun hq => ?_, fun hq => h5 G T Mc M V₁ V₂ Yp I L t c hc hq⟩
  obtain ⟨hU, hLC⟩ := h4 G T Mc M V₁ V₂ Yp I L t c.toCtx15316 hc hq
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.toCtx15313L.ctx.hyp
  have hLc : L ∈ cComp (thompsonJ I) := c.toCtx15313L.conc.1
  have hLn : ¬ L ≤ M ⊓ I := c.toCtx15313L.conc.2.1
  have hLle : L ≤ I := le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ hLc)
  have hNM : Subgroup.normalizer (V₁ : Set G) ≤ M :=
    (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU.1).1
  exact hLn (le_inf (fun l hl => hNM (Subgroup.centralizer_le_normalizer _ (hLC hl))) hLle)

end SBd4

end CFSG.Quasithin
