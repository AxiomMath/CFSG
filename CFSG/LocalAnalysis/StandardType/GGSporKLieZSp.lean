module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSpCent
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZQuot
import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open Matrix

theorem pCoreSevenTrivial_StatedSp {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    PCoreSevenTrivial ↥(StatedSp n K) := by
  intro x hx
  haveI : Fintype K := Fintype.ofFinite K
  have hodd : Odd (orderOf (x : GL (Fin n ⊕ Fin n) K)) := by
    rw [Subgroup.orderOf_coe, hx]
    norm_num
  have hcent : Subgroup.centralizer ({x} : Set ↥(StatedSp n K)) =
      (Subgroup.centralizer ({(x : GL (Fin n ⊕ Fin n) K)} :
        Set (GL (Fin n ⊕ Fin n) K))).comap (StatedSp n K).subtype := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_comap,
      Subgroup.mem_subgroupOf, Subgroup.coe_subtype, Set.mem_singleton_iff, forall_eq]
    exact Subtype.ext_iff
  rw [hcent]
  exact pCoreOf_centralizer_StatedSp_eq_bot (x : GL (Fin n ⊕ Fin n) K) x.2 hodd

theorem lieZRow_PSp {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    LieZRow (StatedProj (StatedSp n K)) := by
  have hZ : Nat.Coprime 14 (Nat.card ↥((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf
      (StatedSp n K))) := by
    rw [CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot,
      Subgroup.card_bot]
    exact Nat.coprime_one_right 14
  exact lieZRow_statedProj (StatedSp n K) hZ
    (lieZRow_of_pCoreSevenTrivial (pCoreSevenTrivial_StatedSp n))

end CFSG.StandardType.SporadicShape
