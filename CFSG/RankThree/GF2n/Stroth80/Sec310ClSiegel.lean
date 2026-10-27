module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClSiegelEichler
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaElementary
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClLemmaPElem
public import CFSG.RankThree.GF2n.Stroth80.Sec310Assembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

namespace Classify

private theorem exists_ne_zero_ne_one {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun c _ => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (h c hc)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at h1
  omega

theorem siegelGenStatement_holds : SiegelGenStatement := by
  intro K V _ _ _ _ _ _ Qf h4K hQ h4 _
  rw [closure_siegel_eq_elementaryGroup hQ, orthSubgroup_eq_orthogonalGroup]
  refine commutator_orthogonalGroup_eq_elementaryGroup_of_plusTwo (fun K _ _ _ h4K => ?_) Qf
    h4K hQ h4
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one h4K
  exact commutator_orthogonalGroup_quadPlus_two K hc0 hc1

end Classify

theorem stroth310_of_mcLaughlin (h34 : Stroth34Statement) (hMcL : McLaughlinStatement) :
    Stroth310Statement :=
  stroth310_of_34 h34 (stroth310Classify_of_mcLaughlin h34 hMcL Classify.siegelGenStatement_holds)

end CFSG.RankThree.GF2n.Stroth80
