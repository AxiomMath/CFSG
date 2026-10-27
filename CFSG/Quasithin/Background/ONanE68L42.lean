module

public import CFSG.Quasithin.Background.ONanE68S8
public import CFSG.Quasithin.Background.ONanE68Small

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68 CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Blueprint

section L42

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem nonempty_equiv_alt_eight_of_psl_four_two {X : Type} [Group X]
    (h : LowTwoRank.StatedClassicalModel X .PSL 4 2 1) :
    Nonempty (X ≃* alternatingGroup (Fin 8)) :=
  have hmem : (LowTwoRank.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel (Or.inl ⟨hmem, h⟩)

theorem case3_of_l42 (hInn : Ch1.EvenLieAutInner) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hmodel : LowTwoRank.StatedClassicalModel ↥L .PSL 4 2 1)
    (hout : ∃ s ∈ T ⊓ Subgroup.centralizer (V : Set G), InducesOuter s L) :
    E68Case3 T M V U L := by
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 4 2 1 hmodel).2
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_quasisimple hq hs
  obtain ⟨e8⟩ := nonempty_equiv_alt_eight_of_psl_four_two hmodel
  have hLM := not_le_of_component h hU.1 hL
  have hle : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 :=
    relIndex_le_two_of_inner_cyc (baseHyp h hU hL) hZ
      (fun β hβ hP => hInn ↥L (Or.inr ⟨4, Or.inl rfl, hmodel⟩) β hβ hP)
      (fun P => isCyclic_center_sylow_of_stated_psl_binary (Or.inr (Or.inl rfl)) hmodel P)
  have hm := mQuot_eq_one_of_relIndex_le_two h hLM hle
  exact ⟨hmodel, nonempty_quot_perm_eight h.isPGroup_Q hQN hq hs e8 hout,
    fun hHM => eq_inf_centralizer_of_hypOrMax h hU hL hHM, hm,
    rParam_eq_one_of h inf_le_left hm fun hC => hLM ((le_centralizer_inf_centralizer V L).trans hC)⟩

end L42

end E68Proof

end E6

end CFSG.Quasithin
