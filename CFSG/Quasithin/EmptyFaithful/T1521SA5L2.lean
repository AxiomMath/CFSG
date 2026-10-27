module

public import CFSG.Quasithin.EmptyFaithful.T1521SA5Wr
public import CFSG.Quasithin.EmptyFaithful.T1521SA5Orb
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Basic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

private theorem isComponentIn_of_isComponentOf_aux {L X : Subgroup G} (h : IsComponentOf L X) :
    IsComponentIn L X := by
  have h1 := CFSG.Assembly.isComponentOf_iff_open.mpr h
  exact ⟨h.1, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).1
    h1⟩

variable [Finite G]

private theorem commutator_conjByElt_eq_bot_aux {X L : Subgroup G} {t : G}
    (hc : IsComponentOf L X) (htX : t ∈ X) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅L, conjByElt t L⁆ = ⊥ := by
  have hL := isComponentIn_of_isComponentOf_aux hc
  have hL' : IsComponentIn (conjByElt t L) X := Unc25G2.isComponentIn_map_conj hL htX
  refine (BenderBranch.eq_or_commute_of_isComponentIn hL hL').resolve_left fun h => htn ?_
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm

theorem exc1521_two_of_orbits (horb : A3Orbits G) {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hco : IsComponentOf L X) (hL : IsPSL 2 2 2 ↥L)
    (hnot : ¬ thompsonJ S ≤ innerPart1521 S L) : Exc1521 X S L := by
  obtain ⟨hXS, hcase⟩ := horb X S L hStd.sqtk hStd.sylow hStd.comp
  intro p Y hp hYX hYJ _ hY _
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_orbits hXS (hcase.imp id fun h => by
      obtain ⟨t, htS, -, hset, -⟩ := h
      exact ⟨t, htS, hset⟩) hYX (exists_odd_pow_eq_one_of_isPGroup hp hY)
  have hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G) := by
    rcases hcase with hnorm | ⟨t, htS, htn, hset, -⟩
    · exact (thompsonJ_le_self S).trans fun s hs => hnorm s hs
    · have hcomm := commutator_conjByElt_eq_bot_aux hco (hStd.sylow.1 htS) htn
      exact iSup₂_le fun A hA => le_normalizer_of_wreath_two hL hStd.sylowL hset hcomm hA
  exact centralizes_two_of_thompsonJ_le hStd hL hJN hnot hp hYJ hYL hY

theorem dich1521L2_two_of_orbits (horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) :
    Dich1521L2Two := by
  intro G _ _ X S L hStd hco _ hL
  by_cases hB : oTwoUpper (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (thompsonJ S : Set G)
  · exact Or.inl (nrm1521_of_psl2_borel le_rfl hL hStd.sylowL hB)
  · refine Or.inr (exc1521_two_of_orbits (horb G) hStd hco hL fun hJ => hB ?_)
    exact (oTwoUpper_le _).trans (borel_le_normalizer_thompsonJ_of_le hJ)

end CFSG.Quasithin
