module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtRecOn_sp :
    GGL45NtRecOn GGL45NtFamSp := by
  intro p hp hp2 lab hlab hkg hSp Q hraw
  obtain ⟨t, l, n⟩ := lab
  rcases hSp.2 with ht | ht <;> dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hraw ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (m := l) (N := 2 ^ n)
      (Q := GGL45NtRec p) (fun K _ _ hK => ?_) hraw
    intro _ _
    have hl2 : 2 ≤ l := hlab.2.1
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    haveI : NeZero l := ⟨by omega⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r
      exact (RecipeFieldSp.mem_conjImage_iff_inn (K := K) (m := l)).mpr ⟨r, rfl⟩
    · intro u hu _
      exact ((RecipeFieldSp.mem_conjImage_iff_inn (K := K) (m := l)).mp hu).imp
        fun r hr => hr.symm
    · exact ggCenterPrime_sp (K := K) (m := l) hp hp2
  · dsimp only [LargeEvenRawDatum] at hraw ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (m := l) (N := 2 ^ n)
      (Q := GGL45NtRec p) (fun K _ _ hK => ?_) hraw
    intro _ _
    have hl2 : 2 ≤ l := hlab.2.1
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    haveI : NeZero l := ⟨by omega⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r
      exact (RecipeFieldSp.mem_conjImage_iff_inn (K := K) (m := l)).mpr ⟨r, rfl⟩
    · intro u hu _
      exact ((RecipeFieldSp.mem_conjImage_iff_inn (K := K) (m := l)).mp hu).imp
        fun r hr => hr.symm
    · exact ggCenterPrime_sp (K := K) (m := l) hp hp2

end CFSG.StandardType
