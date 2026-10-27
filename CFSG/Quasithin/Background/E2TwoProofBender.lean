module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2P

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem ASHyp.isBorelIn_of_bender (hX : ASHyp K T M) (hB : fusionIsBenderGroup ↥K) :
    E2.IsBorelIn K (M ⊓ K) := by
  have hS := hX.isSylow_inf
  have := hX.simple
  have hle : (M ⊓ K).subgroupOf K ≤
      Subgroup.normalizer (((toSylow2 hS : Sylow 2 ↥K) : Subgroup ↥K) : Set ↥K) := by
    refine Bridge.Over.le_normalizer_of_bender hB (toSylow2 hS) ?_ ?_
    · rw [toSylow2_coe]
      exact Subgroup.subgroupOf_mono K hX.inf_le_inf_M
    · intro h
      apply hX.inf_M_ne
      exact le_antisymm inf_le_right fun x hx => (Subgroup.subgroupOf_eq_top.mp h) hx
  rw [toSylow2_coe] at hle
  refine ⟨T ⊓ K, hS, le_antisymm (fun x hx => ⟨hx.2, ?_⟩)
    (le_inf hX.normalizer_le_M inf_le_left)⟩
  have h1 := (mem_normalizer_map_iff_of_injective (f := K.subtype) K.subtype_injective).mpr
    (hle (show (⟨x, hx.2⟩ : ↥K) ∈ (M ⊓ K).subgroupOf K from hx))
  rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1

theorem e22BenderFam : E22BenderFam := by
  intro X _ _ K T M hX n ⟨hn, h⟩
  refine hX.isBorelIn_of_bender ?_
  rcases h with h | h | h
  · exact A5.C25.fusionIsBenderGroup_of_isPSL h
  · exact A5.C25.fusionIsBenderGroup_of_isSz h
  · exact K1.fusionIsBenderGroup_of_stated_psu_three hn h

end E2P

end CFSG.Quasithin
