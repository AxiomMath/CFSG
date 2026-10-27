module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeNine
public import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LieType.BorelTits Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nineH_subgroupOf_normal (V K : Subgroup G) :
    ((nineH V K).subgroupOf K).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Nine3Choice.nineH_le_K (V := V) (K := K))).mpr ?_
  intro k hk
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hmap : conjSubgroup (nineH V K) k =
      ⨆ U ∈ omegaIn V K (nineE V K), conjSubgroup U k := by
    dsimp only [nineH]
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
  rw [hmap]
  refine Subgroup.eq_of_le_of_card_ge
    (iSup₂_le fun U hU => le_iSup₂_of_le (conjSubgroup U k) (conjSubgroup_mem_omegaIn hU hk)
      le_rfl) ?_
  rw [← hmap, E3.card_conjSubgroup]

theorem pCoreOf_nineH_le_pCoreOf (V K : Subgroup G) :
    pCoreOf 2 (nineH V K) ≤ pCoreOf 2 K :=
  CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
    (Nine3Choice.nineH_le_K (V := V) (K := K))
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Nine3Choice.nineH_le_K (V := V) (K := K))).mp (nineH_subgroupOf_normal V K))

end CFSG.LocalAnalysis.WeakClosure81
