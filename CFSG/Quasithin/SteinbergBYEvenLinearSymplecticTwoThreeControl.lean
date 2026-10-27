module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.Quasithin.SteinbergBITwoThreeSL2

public section

namespace CFSG.Quasithin.SteinbergBY

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.SteinbergBI

section Linear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

variable {K : Type} [Field K]

theorem exists_projectiveSL_of_statedPSL {S : Type} [Group S] {n f : ℕ}
    (hS : StatedClassicalModel S .PSL n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (S ≃* projectiveSL n K) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  exact ⟨K, inferInstance, inferInstance, hK, ⟨(e.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩

theorem two_dvd_card_of_statedPSL {S : Type} [Group S] {n f : ℕ}
    (hS : StatedClassicalModel S .PSL n 2 f) : 2 ∣ Nat.card S := by
  have hn : 2 ≤ n := hS.1.2.2.1
  have hf : 1 ≤ f := hS.1.2.1
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := exists_projectiveSL_of_statedPSL hS
  rw [Nat.card_congr φ.toEquiv]
  refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card (projUnitriangular n K))
  rw [card_projUnitriangular, hK, ← pow_mul]
  refine dvd_pow_self 2 ?_
  have : 1 ≤ n * (n - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc 1 * 2 = 2 * 1 := by norm_num
      _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))

end Linear

end CFSG.Quasithin.SteinbergBY
