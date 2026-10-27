module

public import CFSG.GroupTheory.SteinbergBKFittingChiefDetection

public section

namespace CFSG.LocalAnalysis

open scoped commutatorElement

theorem solvable_fitting_centralizes_chief_factors {G : Type*} [Group G] [Finite G]
    (hG : Group.IsSolvable G) {Q : Subgroup G} (hQ : Q.Normal) {X Y : Subgroup G}
    (hX : X.Normal) (hY : Y.Normal) (hYX : Y < X)
    (hchief : ∀ Z : Subgroup G, Z.Normal → ¬ (Y < Z ∧ Z < X)) :
    ⁅(fittingSubgroup Q).map Q.subtype, X⁆ ≤ Y := by
  set cf := CFSG.GroupTheory.SteinbergBK.chiefFactorOfPair hX hY hYX hchief
  have hle := normal_nilpotent_le_centralizerOfChiefFactor_top hG (fittingSubgroupOf Q)
    (fittingSubgroupOf_normal Q hQ) (fittingSubgroupOf_isNilpotent Q) cf
  rw [Subgroup.commutator_le]
  intro n hn x hx
  have h := (Subgroup.mem_inf.mp (hle hn)).2
  exact h x hx

end CFSG.LocalAnalysis
