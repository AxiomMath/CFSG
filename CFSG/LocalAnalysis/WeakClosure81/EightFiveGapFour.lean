module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFourOrthBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFourWreath

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem w3Lem85TwoGap4_holds : W3Lem85TwoGap4 := by
  intro X _ _ S hS h2 hshape hc
  let φ : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : Odd (Nat.card φ.ker) := by
    rw [QuotientGroup.ker_mk']
    exact odd_card_center_of_pCore_eq_bot hS.pCore_eq_bot
  obtain ⟨d, hdd, -, hSd, hcl⟩ := barSituation_map_two hS h2 φ hφ hker
  have hcs := centralInSylow_map φ hφ S hc
  rw [hSd] at hcs
  have hnc : Subgroup.normalClosure ({d} : Set (X ⧸ Subgroup.center X)) = ⊤ := by
    have hset : Group.conjugatesOfSet ({d} : Set (X ⧸ Subgroup.center X)) =
        {y | IsConj d y} := by
      ext y
      simp [Group.mem_conjugatesOfSet_iff]
    rw [Subgroup.normalClosure, hset]
    exact hcl.2.2
  rcases hshape with ⟨m, n, hY⟩ | ⟨n, m, hm, hY⟩
  · exact not_centralInSylow_of_isOrthGp hY d hdd hnc hcs
  · exact not_centralInSylow_of_isL2WrSymGp hm hY d hnc hcs

end CFSG.LocalAnalysis.WeakClosure81

end
