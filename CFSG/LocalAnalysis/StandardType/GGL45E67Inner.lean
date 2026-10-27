module

public import CFSG.LocalAnalysis.StandardType.GGL45FamCover
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45E67_pow_three_mem_inn :
    GGL45NtOn GGL45FamE67 fun _ _ R _ I _ =>
      ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only [GGL45FamE67] at hS
  obtain ⟨-, htag⟩ := hS
  rcases htag with rfl | rfl | rfl
  · dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQK, ?_⟩
    intro φ hφ
    obtain ⟨r, hr⟩ := TableBExc.pow_three_mem_inn_of_mem_recipeID_E6 hφ
    exact ⟨r, hr.symm⟩
  · dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQK, ?_⟩
    have hn : 1 ≤ n := by
      have h := hlab
      dsimp only [LargeEvenInLambda2] at h
      exact h.1
    intro φ hφ
    obtain ⟨r, hr⟩ := TwE6Delta.pow_three_mem_inn hn hK hφ
    exact ⟨r, hr.symm⟩
  · dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQK, ?_⟩
    have hchar : CharP K 2 := charP_two_of_card hK
    change ∀ φ ∈ LargeEvenChevIDImage (CFSG.Blueprint.Chevalley.Tag.E7).cartan K
        (LargeEvenChevH (CFSG.Blueprint.Chevalley.Tag.E7).cartan K false),
      ∃ r : LargeEvenCenterQuot
        (LargeEvenChevH (CFSG.Blueprint.Chevalley.Tag.E7).cartan K false),
        φ ^ 3 = MulAut.conj r
    intro φ hφ
    have hT : TableB.torusSubgroup (CFSG.Blueprint.Chevalley.Tag.E7).cartan K = ⊤ :=
      TableB.torusSubgroup_eq_top_of_mul_eq_smul (LargeEvenCartanE 7) K TableB.cartanE7_adj
        (TableB.exists_sq_eq_of_charTwo K)
    have hsub := chevIDImage_subset_inn_of_top (τ := .E7) hT
    obtain ⟨r, hr⟩ := hsub hφ
    exact ⟨r ^ 3, by rw [← hr, ← map_pow]⟩

end CFSG.StandardType
