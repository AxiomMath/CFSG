module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1CentrelessFacts
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FbElem
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FbG23
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FbU43
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FbMcL

public section

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def SylowThreeNotRankTwoByCyclicJ3 : Prop :=
  ∀ (P : Type) [Group P] [Finite P], Nonempty (P ≃* Blueprint.NativeSporadic.J3) →
    ∀ T : Sylow 3 P, ¬ IsRankTwoByCyclic ↥(T : Subgroup P)

section Certified


theorem sylowThreeNotRankTwoByCyclic_of_J3 (hJ3 : SylowThreeNotRankTwoByCyclicJ3) :
    SylowThreeNotRankTwoByCyclic := by
  intro P _ _ hB T
  obtain hG | hU | hJ | hM := hB
  · obtain ⟨E, hc, h3, hcard⟩ := exists_elemAbelian81_G23 hG
    exact not_isRankTwoByCyclic_sylow_of_elemAbelian hc h3 hcard T
  · obtain ⟨e⟩ := hU
    obtain ⟨E, hc, h3, hcard⟩ := exists_elemAbelian81_U43 e
    exact not_isRankTwoByCyclic_sylow_of_elemAbelian hc h3 hcard T
  · exact hJ3 P hJ T
  · obtain ⟨e⟩ := hM
    obtain ⟨E, hc, h3, hcard⟩ := exists_elemAbelian81_McL e
    exact not_isRankTwoByCyclic_sylow_of_elemAbelian hc h3 hcard T

end Certified

end CFSG.RankThree.PartTwo.Sec11
