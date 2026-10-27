module

public import CFSG.LocalAnalysis.WeakClosure81.Eleven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def elevenBlocks (M U : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ T : Sylow 2 ↥(Subgroup.centralizer (U : Set G)),
    ∃ Y' ∈ blocksStar (T : Subgroup ↥(Subgroup.centralizer (U : Set G))),
      Y'.map (Subgroup.centralizer (U : Set G)).subtype = Y ∧ ¬ Y ≤ M}

theorem isBlockOfInX_of_mem_elevenBlocks {M U Y : Subgroup G} (hY : Y ∈ elevenBlocks M U) :
    IsBlockOfInX (Subgroup.centralizer (U : Set G)) Y := by
  obtain ⟨T, Y', hY', rfl, -⟩ := hY
  have hle : Y'.map (Subgroup.centralizer (U : Set G)).subtype ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.map_subtype_le _
  refine (isBlockInX_subgroupOf_iff hle).1 ?_
  have : (Y'.map (Subgroup.centralizer (U : Set G)).subtype).subgroupOf
      (Subgroup.centralizer (U : Set G)) = Y' :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.centralizer (U : Set G)).subtype_injective Y'
  rw [this]
  exact hY'.1

theorem exists_mem_elevenBlocks {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hU : U ∈ gammaEleven M V) : ∃ Y, Y ∈ elevenBlocks M U := by
  classical
  by_contra hno
  have hno' : ∀ Y, Y ∉ elevenBlocks M U := fun Y hY => hno ⟨Y, hY⟩
  have hQH : IsSylowOf 2 Q (Subgroup.centralizer (U : Set G)) :=
    eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hU
  obtain ⟨T, hT⟩ := sylow_of_isSylowOf hQH
  have hTQ : Subgroup.map (Subgroup.centralizer (U : Set G)).subtype ↑T = Q := by
    rw [hT]; exact Subgroup.map_subgroupOf_eq_of_le hQH.1
  have h3 := eleven_three_uncond rfl hset hK hU T hTQ
  have hbot : (⨆ Y ∈ blocksStar (T : Subgroup ↥(Subgroup.centralizer (U : Set G))),
      ⨆ (_ : ¬ Subgroup.map (Subgroup.centralizer (U : Set G)).subtype Y ≤ M), Y) = ⊥ := by
    refine le_bot_iff.1 (iSup₂_le fun Y hY => iSup_le fun hYM => ?_)
    exact absurd ⟨T, Y, hY, rfl, hYM⟩ (hno' _)
  rw [hbot, sup_bot_eq, top_inf_eq] at h3
  exact hU.2.2.1 (Subgroup.subgroupOf_eq_top.1 h3.symm)

private theorem conjSubgroup_iSup' {ι : Sort*} (A : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, A i) g = ⨆ i, conjSubgroup (A i) g :=
  Subgroup.map_iSup _ _

end CFSG.LocalAnalysis.WeakClosure81
