module

public import CFSG.Quasithin.EmptyFaithful.S153D28

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure Concl15329 {G : Type} [Group G] [Finite G] (T M V₁ Yp I : Subgroup G) : Prop where
  no_char : ∀ C : Subgroup G, C ≤ Sgp153 T V₁ → C ≠ ⊥ →
    (C.subgroupOf (Sgp153 T V₁)).Characteristic → ¬ I ≤ Subgroup.normalizer (C : Set G)
  norm_le : Subgroup.normalizer (V₁ : Set G) ≤ M
  cent : Yp ≤ Subgroup.centralizer (V₁ : Set G)

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem lemma_15_3_29 (h113 : StageLemma14113) (c : Ctx15328 T Mc M V₁ V₂ Yp I L t) :
    Concl15329 T M V₁ Yp I := by
  have hh := c.ctx.hyp
  have hI := c.ctx.inH
  have hcase := c.facts.case_two
  have hLI : L ≤ I := (le_of_mem_cComp c.conc.1).trans (thompsonJ_le_self I)
  have hLM : ¬ L ≤ M := fun h => c.conc.2.1 (le_inf h hLI)
  have hYpY : Yp ≤ Y153 Mc M := hh.Yp_le_Y153
  have h3 := hh.lemma_15_3_11_three h113 hcase hI
  refine ⟨fun C hCS hC1 hchar hIN => ?_, h3.2.1, ?_⟩
  ·
    have hL : ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ L)⁆ ≠ ⊥ := by
      intro hbot
      have hle : oTwoUpper (Y153 Mc M ⊓ L) ≤ Subgroup.centralizer (VZ T M : Set G) :=
        Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
      have hYpO : Yp ≤ oTwoUpper (Y153 Mc M ⊓ L) := by
        rw [← hh.oTwoUpper_eq]
        exact oTwoUpper_mono (le_inf hYpY c.c27.Yp_le)
      have hYV : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ≤
          Subgroup.centralizer (VZ T M : Set G) := by
        rw [← hcase.2]
        exact hYpO.trans hle
      exact hh.hyp.Yplus_not_le_centralizer h113 hh.decomp hYV
    refine hh.hyp.lemma_15_3_11_twelve hh.decomp hL hLM hCS hC1 hchar ?_
    rw [← c.I_eq]
    exact hIN
  · rw [hcase.2]
    exact (oTwoUpper_le _).trans inf_le_right

end S153D

end CFSG.Quasithin
