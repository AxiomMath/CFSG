module

public import CFSG.RankThree.PartOne.KP.BReduction
public import CFSG.RankThree.PartOne.KP.BLeviMonster

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LieType.Chevalley.C2E6Std
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def BMonsterData (S : Type) [Group S] : Prop :=
  ∃ (s : S) (K : Subgroup (Subgroup.centralizer ({s} : Set S))), IsQuasisimple K ∧
    Nat.card (Subgroup.center K) = 2 ∧ Nonempty (K ⧸ Subgroup.center K ≃* stdGroup)

theorem sectionsForceEvenRankFour_B_of_monsterData {S : Type} [Group S] [Finite S]
    (ι : Carrier .B ≃* S) (h : BMonsterData S) : SectionsForceEvenRankFour (Carrier .B) := by
  obtain ⟨s, K, hq, hz, ⟨eQ⟩⟩ := h
  obtain ⟨U9, hU9, hc9⟩ := exists_elementary_two_nine
  exact sectionsForceEvenRankFour_of_unitary_levi_component ι hq hz eQ stdLeviIn stdLeviEquiv U9
    hU9 hc9

end CFSG.RankThree.PartOne
