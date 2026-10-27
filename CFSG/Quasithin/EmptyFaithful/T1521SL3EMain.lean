module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3EModel
public import CFSG.Quasithin.EmptyFaithful.T1521SFam
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Basic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.L31521E

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem isComponentIn_of_isComponentOf1521 {L X : Subgroup G} (h : IsComponentOf L X) :
    IsComponentIn L X := by
  have h1 := CFSG.Assembly.isComponentOf_iff_open.mpr h
  exact ⟨h.1, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).1
    h1⟩

variable [Finite G]

theorem commutator_conjByElt_eq_bot1521 {X L : Subgroup G} {t : G} (hc : IsComponentOf L X)
    (htX : t ∈ X) (htn : t ∉ Subgroup.normalizer (L : Set G)) : ⁅L, conjByElt t L⁆ = ⊥ := by
  have hL := isComponentIn_of_isComponentOf1521 hc
  have hL' : IsComponentIn (conjByElt t L) X := Unc25G2.isComponentIn_map_conj hL htX
  refine (BenderBranch.eq_or_commute_of_isComponentIn hL hL').resolve_left fun h => htn ?_
  exact mem_normalizer_of_conjByElt_eq' h.symm

end CFSG.Quasithin.L31521E

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L31521E

theorem e1L3_of (h37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) : E1L3 := by
  intro G _ _ X S L hStd hco _ ⟨n, hn, hL⟩
  obtain ⟨-, hcase⟩ := a3Orbits_of_a37_a38 h37 h38 X S L hStd.sqtk hStd.sylow hStd.comp
  obtain ⟨V, V', hB⟩ := rankBound1521_l3 (by omega) hL (isQuasisimple_of_open1521 hco.2.2)
    hStd.sylowL
  rcases hcase with hnorm | ⟨t, htS, htn, hset, -, -, -⟩
  · exact thompsonJ_le_innerPart_of_bound hB fun t ht => hnorm t ht
  · exact thompsonJ_le_innerPart_of_bound_wreath hB hset
      (commutator_conjByElt_eq_bot1521 hco (hStd.sylow.1 htS) htn)

end CFSG.Quasithin
