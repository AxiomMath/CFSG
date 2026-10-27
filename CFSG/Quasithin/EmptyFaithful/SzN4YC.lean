module

public import CFSG.Quasithin.EmptyFaithful.SzN4Core

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section YC

variable {G : Type} [Group G] [Finite G]

theorem szN4_yc_central (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kS : Lin2Setup) (kL : Lin2YLLabel) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) (hsh : IsShort2 L)
    (hYY : Yp = Y153 Mc M) (hYLV : ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G)) :
    YC153 Yp L ≤ Subgroup.centralizer (L : Set G) := by
  have hlab := kL G T Mc M V₁ V₂ Yp I L t ctx hn hYLV
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := hh.decomp.model
  have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    hh.hyp.Sgp153_le_normalizer_V₂ hh.decomp
  have hSV₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hlift : ∀ g : G, g ∈ T → ∀ hgN : g ∈ Subgroup.normalizer (VZ T M : Set G),
      convI hV ⟨g, hgN⟩ ∈ L₁ ⊔ L₂ → g ∈ Sgp153 T V₁ := by
    intro g hgT hgN hmem
    refine ⟨hgT, ?_⟩
    rw [hV₁]
    exact (mem_normalizer_map_inclMod_iff hV hgN (commV L₁)).2 (hS.sup_le_stab₁ hmem)
  rcases hlab with hl | hl
  · exact szN4_core h113 h37 h38 kS ctx hn hsh hYY hS hV₁ hV₂ hSV₁ hlift hl
  · exact szN4_core h113 h37 h38 kS ctx hn hsh hYY hS.symm hV₂ hV₁ hSV₂
      (fun g hgT hgN hmem => hlift g hgT hgN (by rwa [sup_comm] at hmem)) hl

end YC

end CFSG.Quasithin
