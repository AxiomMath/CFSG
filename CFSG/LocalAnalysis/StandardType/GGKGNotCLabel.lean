module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGKGNotCDefs

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

theorem kg_false_of_notC
    {X : Type} [Group X] {k f : ℕ} (hk : 3 ≤ k) (h : KGNotCLieType 2 X)
    (hC : GGHasLabel ⟨.C, k, f⟩ (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨t, r, e, ht, hm⟩ := h
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
    dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hC
    obtain ⟨K, hKfield, hKfin, _, hproj⟩ := hC
    obtain ⟨eC⟩ := hproj
    refine CFSG.StandardType.center_eq_bot_of_mulEquiv_of_center_eq_bot eC.symm ?_
    exact CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (k := K) (r := k)
      (by omega)
  obtain ⟨lab', hl', htag, -, -, -, hraw⟩ :=
    CFSG.StandardType.exists_label_rawDatum_of_lieModel hZ hm
  rcases (kg_rigid_C hk hC hl' hraw).1 with hB | hCtag
  · have hpsp : t = .PSp := by
      rw [← htag]
      simp [markTag, hB]
    exact ht hpsp
  · have hpsp : t = .PSp := by
      rw [← htag]
      simp [markTag, hCtag]
    exact ht hpsp

end CFSG.StandardType.KG
