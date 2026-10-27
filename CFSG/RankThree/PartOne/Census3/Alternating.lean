module

public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen

public section

namespace CFSG.RankThree.PartOne.Census3

open TauCeti
open CFSG.RankThree.GroupTheory
  (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four)

theorem theoremThreeCase_alternating (n : ℕ) (hn : 5 ≤ n) :
    TheoremThreeCase (.alternating n hn) := by
  intro G _ _ hG e
  by_cases h12 : n ≤ 12
  · exact TheoremThreeList.of_alternating hn h12 e
  · exfalso
    let π : (⊤ : Subgroup G) →* alternatingGroup (Fin n) :=
      e.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom
    have hinj : Function.Injective π := e.injective.comp Subgroup.topEquiv.injective
    have hZ : π.ker ≤ Subgroup.center (⊤ : Subgroup G) := by
      intro x hx
      rw [(MonoidHom.ker_eq_bot_iff π).mpr hinj, Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.one_mem _
    exact h12 ((alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
      π (e.surjective.comp Subgroup.topEquiv.surjective) hZ).2.2.1 hG.twoLocalOddRank_le)

end CFSG.RankThree.PartOne.Census3
