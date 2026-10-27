module

public import CFSG.Quasithin.EmptyFaithful.S153D0JCase
public import CFSG.Quasithin.EmptyFaithful.S153D13
public import CFSG.Quasithin.EmptyFaithful.S153D0Facts
public import CFSG.Quasithin.EmptyFaithful.S153D0J
public import CFSG.Quasithin.EmptyFaithful.S153Five

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem inf_centralizer_le_R153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) (hYp : Yp ≤ Y153 Mc M) :
    T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (Yp ⊔ Sgp153 T V₁) := by
  have hC : pCoreOf 2 (Y153 Mc M ⊔ T) = T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    h.lemma_15_3_7_pCore h113
  have hCS : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Sgp153 T V₁ :=
    inf_le_inf_left T ((Subgroup.centralizer_le D.le₁).trans
      (Subgroup.centralizer_le_normalizer _))
  have hn : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) := by
    have := le_normalizer_pCoreOf 2 (Y153 Mc M ⊔ T)
    rw [hC] at this
    exact (sup_le_sup hYp inf_le_left).trans this
  exact le_pCoreOf_of_le_normalizer 2 (hCS.trans le_sup_right) hn
    (h.qtfe.sylow.1.to_le inf_le_left)

theorem R_eq_of_hyp (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hr : CFSG.Open.pRank 3 Yp = 2) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    R153 T V₁ Yp = T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  rcases h.cases with hY | ⟨-, hY⟩
  · exact (h.lemma_15_3_11_five_case_one h113 hY).2.1
  · have hsyl := h.lemma_15_3_11_one h11 h113 hI
    have hsylR : IsSylowTwoOf (Sgp153 T V₁) (Yp ⊔ Sgp153 T V₁) :=
      A4.isSylowTwoOf_mono hsyl le_sup_right hI.1.1
    have hYpY : Yp ≤ Y153 Mc M := h.Yp_le_Y153
    refine le_antisymm ?_ (inf_centralizer_le_R153 h113 h.hyp h.decomp hYpY)
    rw [hY] at hr hsylR ⊢
    exact R_le_of_case_two h113 h.hyp h.decomp hr hsylR

theorem J_not_le_of_hyp (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    ¬ autOn (thompsonJ I) (UI153 T I) ≤ autOn (M ⊓ I) (UI153 T I) := by
  intro hle
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hJMI : thompsonJ I ≤ M ⊓ I :=
    le_of_autOn_le hUN (thompsonJ_le_self I) inf_le_right (h.lemma_15_3_11_two h113 hI) hle
  by_cases hJT : thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)
  · exact hI.2 (le_of_thompsonJ_le_of_centralizes h11 h (h.lemma_15_3_11_one h11 h113 hI) hJT
      (hJMI.trans inf_le_left))
  · exact not_thompsonJ_le_M_of_not_le h11 h113 h hI hJT (hJMI.trans inf_le_left)

theorem facts15311_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hr : CFSG.Open.pRank 3 Yp = 2) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) : Facts15311 T M V₁ Yp I :=
  facts15311_of_partial h11 h113 h hI (h.hyp.struct_of_le h113 h.Yp_le_Y153 hr)
    (R_eq_of_hyp h11 h113 h hr hI) (J_not_le_of_hyp h11 h113 h hI)

theorem facts15311All_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113) :
    Facts15311All := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr I hI
  exact facts15311_of_stages h11 h113 h hr hI

end S153D

theorem theorem15313_of_stages
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (h15 : Input15315Two) (h16 : Input15316One) (h17 : Input15317)
    (h18 : Input15318) (h19 : Input15319) (h20 : Input15320) (h21 : Input15321)
    (h23 : Input15323) (h24 : Input15324) : Stage15313 :=
  theorem15313_of_inputs hC27 h37 h38 hcover (S153D.facts15311All_of_stages h11 h113) h15 h16 h17
    h18 h19 h20 h21 h23 h24

end CFSG.Quasithin
