module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtRecOn_orth :
    GGL45NtRecOn GGL45NtFamOrth := by
  intro p hp hp2 lab hlab _hkg hS
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨-, hvac, hexc⟩, hlin, huni, hsp⟩ := hS
  have ht : t = .D ∨ t = .twD := by
    cases t <;> simp_all [GGL45NtVacLabel, GGL45NtExcLabel, GGL45NtLinLabel,
      GGL45NtUniLabel, GGL45NtSpLabel]
  have h4 : 4 ≤ l := by
    rcases ht with h | h
    · have hlab' := hlab
      rw [h] at hlab'
      dsimp only [LargeEvenInLambda2] at hlab'
      have h3 : l ≠ 3 := by
        intro hl3
        exact hlin (by rw [h]; exact Or.inr ⟨rfl, hl3⟩)
      omega
    · have hlab' := hlab
      rw [h] at hlab'
      dsimp only [LargeEvenInLambda2] at hlab'
      have h2 : l ≠ 2 := by
        intro hl2
        exact hvac (by rw [h]; exact Or.inr (Or.inl ⟨rfl, hl2⟩))
      have h3 : l ≠ 3 := by
        intro hl3
        exact huni (by rw [h]; exact Or.inr ⟨rfl, hl3⟩)
      omega
  rcases ht with h | h
  · subst h
    refine largeEvenLabelAll_omegaPlus (P := GGL45NtRec p) rfl h4 ?_
    intro K _ _ _ hK hs hna
    refine ⟨fun r => ⟨r, rfl⟩, fun u hu _ => hu.imp fun r hr => hr.symm, ?_⟩
    exact CorFourTwoOpen.ggCenterPrime_omegaPlus (K := K) (m := l) hp hp2 (by omega)
  · subst h
    refine largeEvenLabelAll_omegaMinus (P := GGL45NtRec p) rfl h4 ?_
    intro K _ _ _ hK b c hbc hs hna
    refine ⟨fun r => ⟨r, rfl⟩, fun u hu _ => hu.imp fun r hr => hr.symm, ?_⟩
    exact CorFourTwoOpen.ggCenterPrime_omegaMinus (K := K) (m := l - 1) hp hp2 (by omega) hbc

end CFSG.StandardType
