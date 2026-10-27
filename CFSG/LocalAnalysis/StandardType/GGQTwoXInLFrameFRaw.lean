module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFRecipe
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_ggQTwoFRRecipe_of_rawDatum {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) (hn : lab.n = 1)
    {Q : LargeEvenRawCont} (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), GGQTwoFRRecipe R I ∧ Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  have hn' : n = 1 := hn
  subst hn'
  cases t <;> dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h <;> try (simp at htag; done)
  · obtain ⟨K, _, _, hK, hq⟩ := h
    exact ⟨LargeEvenProj (LargeEvenSpGroup K l), inferInstance, _, _,
      ggQTwoFRRecipe_sp (by norm_num [hK]) l, hq⟩
  · obtain ⟨K, _, _, hK, hq⟩ := h
    exact ⟨LargeEvenProj (LargeEvenSpGroup K l), inferInstance, _, _,
      ggQTwoFRRecipe_sp (by norm_num [hK]) l, hq⟩
  · by_cases h3 : l = 3
    · simp only [h3, if_true] at h
      obtain ⟨K, _, _, hK, hq⟩ := h
      exact ⟨LargeEvenProj (LargeEvenSLGroup (Fin 4) K), inferInstance, _, _,
        ggQTwoFRRecipe_linearFour (by norm_num [hK]), hq⟩
    · simp only [h3, if_false] at h
      obtain ⟨K, _, _, hK, hq⟩ := h
      exact ⟨LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l)), inferInstance, _, _,
        ggQTwoFRRecipe_omegaPlus (by norm_num [hK]) l, hq⟩
  · by_cases h2 : l = 2
    · simp only [h2, if_true] at h
      obtain ⟨K, _, _, hK, hq⟩ := h
      exact ⟨LargeEvenProj (LargeEvenSLGroup (Fin 2) K), inferInstance, _, _,
        ggQTwoFRRecipe_linearTwo (by norm_num [hK]), hq⟩
    · simp only [h2, if_false] at h
      by_cases h3 : l = 3
      · simp only [h3, if_true] at h
        obtain ⟨K, _, _, hK, hq⟩ := h
        exact ⟨LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2), inferInstance, _, _,
          ggQTwoFRRecipe_unitaryFour (by norm_num [hK]), hq⟩
      · simp only [h3, if_false] at h
        obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := h
        exact ⟨LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)),
          inferInstance, _, _, ggQTwoFRRecipe_omegaMinus (by norm_num [hK]) (l - 1) hbc, hq⟩

end CFSG.StandardType

end
